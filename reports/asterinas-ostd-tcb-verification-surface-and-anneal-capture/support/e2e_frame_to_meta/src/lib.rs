#![no_std]

pub type Paddr = usize;
pub type Vaddr = usize;

pub const PAGE_SIZE: usize = 4096;
pub const META_SLOT_SIZE: usize = 64;
pub const FRAME_METADATA_BASE_VADDR: Vaddr = 0xffff_e000_0000_0000;

/// Monomorphic extract of `ostd/src/mm/frame/meta.rs` `mapping::frame_to_meta`.
pub const fn frame_to_meta(paddr: Paddr) -> Vaddr {
    let base = FRAME_METADATA_BASE_VADDR;
    let offset = paddr / PAGE_SIZE;
    base + offset * META_SLOT_SIZE
}
