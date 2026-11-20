// Probe of `google/zerocopy`'s internal `TrailingSliceLayout` normal form for flat
// `#[repr(C)]` slice DSTs, and of `validate_cast_and_convert_metadata` on prefix casts.
//
// The inspected fields and functions are crate-private, so this probe is a unit-test
// module meant to be appended to `zerocopy/src/layout.rs` in a checkout of
// `google/zerocopy` at commit ec133ce4d7993775413d852f91c9e3eb2a2a0897. From the
// `zerocopy/` directory of that checkout, run:
//
//   cargo +nightly-2026-09-30 test --lib flat_normal_form_probe -- --nocapture
//
// Recorded output: `support/zerocopy_flat_normal_form_probe_output.txt`.

#[cfg(test)]
mod flat_normal_form_probe {
    use super::*;
    use core::num::NonZeroUsize;

    fn nz(n: usize) -> NonZeroUsize { NonZeroUsize::new(n).unwrap() }

    fn show(name: &str, l: DstLayout) {
        match l.size_info {
            SizeInfo::SliceDst(t) => {
                let (a, p) = t.size_rounding_align_and_phase.components();
                println!("{}: align={} offset={} elem_size={} size_base={} size_align={} size_phase={}",
                    name, l.align.get(), t.offset, t.elem_size, t.size_base, a.get(), p);
            }
            SizeInfo::Sized { size } => println!("{}: sized size={}", name, size),
        }
    }

    #[test]
    fn probe() {
        let u8_ = DstLayout::for_type::<u8>();
        let u16_ = DstLayout::for_type::<u16>();
        let u32_ = DstLayout::for_type::<u32>();
        let d1 = DstLayout::for_repr_c_struct(None, None, &[u32_, DstLayout::for_slice::<u8>()]);
        let d2 = DstLayout::for_repr_c_struct(None, None, &[u16_, u8_, DstLayout::for_slice::<u8>()]);
        let d3 = DstLayout::for_repr_c_struct(None, None, &[u16_, u8_, DstLayout::for_slice::<[u8; 2]>()]);
        let a8 = DstLayout::for_repr_c_struct(Some(nz(8)), None, &[u16_, u8_, DstLayout::for_slice::<u8>()]);
        let a4e3 = DstLayout::for_repr_c_struct(Some(nz(4)), None, &[u8_, DstLayout::for_slice::<[u8; 3]>()]);
        let p2 = DstLayout::for_repr_c_struct(None, Some(nz(2)), &[u8_, DstLayout::for_slice::<u32>()]);
        let p1 = DstLayout::for_repr_c_struct(None, Some(nz(1)), &[u32_, DstLayout::for_slice::<u16>()]);
        show("d1 [u32,[u8]]", d1);
        show("d2 [u16,u8,[u8]]", d2);
        show("d3 [u16,u8,[[u8;2]]]", d3);
        show("align(8) [u16,u8,[u8]]", a8);
        show("align(4) [u8,[[u8;3]]]", a4e3);
        show("packed(2) [u8,[u32]]", p2);
        show("packed(1) [u32,[u16]]", p1);
        for (name, l, lens) in [("d2", d2, [3usize, 4, 5, 6]), ("d3", d3, [3, 4, 5, 6]), ("d1", d1, [4, 5, 8, 9])] {
            for len in lens {
                let r = l.validate_cast_and_convert_metadata(0, len, CastType::Prefix);
                println!("{} prefix bytes_len={} -> {:?}", name, len, r.map_err(|e| match e { MetadataCastError::Size => "Size", MetadataCastError::Alignment => "Alignment" }));
            }
        }
    }
}
