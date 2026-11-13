#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_abi::{BackendRepr, FieldsShape, Scalar, TagEncoding, Variants};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::ty::{self, TyCtxt};

struct LayoutCallbacks {
    label: String,
    out_path: String,
}

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', " ")
}

fn fmt_scalar(s: Scalar) -> String {
    match s {
        Scalar::Initialized { value, valid_range } => {
            format!("Initialized({value:?}, {}..={})", valid_range.start, valid_range.end)
        }
        Scalar::Union { value } => format!("Union({value:?})"),
    }
}

fn fmt_backend_repr(br: BackendRepr) -> String {
    match br {
        BackendRepr::Scalar(s) => format!("Scalar({})", fmt_scalar(s)),
        BackendRepr::ScalarPair { a, b, b_offset } => {
            format!("ScalarPair({}, {}, offset={}B)", fmt_scalar(a), fmt_scalar(b), b_offset.bytes())
        }
        BackendRepr::SimdVector { element, count } => {
            format!("SimdVector({}, count={})", fmt_scalar(element), count.as_u64())
        }
        BackendRepr::SimdScalableVector { element, count, number_of_vectors } => {
            format!("SimdScalableVector({}, count={}, n={})", fmt_scalar(element), count.as_u64(), number_of_vectors.0)
        }
        BackendRepr::Memory { sized } => format!("Memory(sized={sized})"),
    }
}

fn fmt_fields(fs: &FieldsShape<rustc_abi::FieldIdx>) -> String {
    match fs {
        FieldsShape::Primitive => "Primitive".to_string(),
        FieldsShape::Union(n) => format!("Union(count={n})"),
        FieldsShape::Array { stride, count } => format!("Array(stride={}B, count={count})", stride.bytes()),
        FieldsShape::Arbitrary { offsets, in_memory_order } => {
            let offs: Vec<u64> = offsets.iter().map(|o| o.bytes()).collect();
            let ord: Vec<usize> = in_memory_order.iter().map(|i| i.as_usize()).collect();
            format!("Arbitrary(offsets={offs:?}, mem_order={ord:?})")
        }
    }
}

fn fmt_variants(v: &Variants<rustc_abi::FieldIdx, rustc_abi::VariantIdx>) -> String {
    match v {
        Variants::Empty => "Empty".to_string(),
        Variants::Single { index } => format!("Single({})", index.as_usize()),
        Variants::Multiple { tag, tag_encoding, tag_field, variants } => {
            let te = match tag_encoding {
                TagEncoding::Direct => "Direct".to_string(),
                TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
                    format!(
                        "Niche(untagged={}, range={}..={}, start={niche_start})",
                        untagged_variant.as_usize(),
                        niche_variants.start.as_usize(),
                        niche_variants.last.as_usize()
                    )
                }
            };
            format!(
                "Multiple(tag={}, encoding={te}, tag_field={}, count={})",
                fmt_scalar(*tag),
                tag_field.as_usize(),
                variants.len()
            )
        }
    }
}

impl Callbacks for LayoutCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let dl = &tcx.data_layout;
        let spec = &tcx.sess.target;
        let dl_json = format!(
            "{{\"target_triple\": \"{}\", \"llvm_target\": \"{}\", \"data_layout\": \"{}\", \"endian\": \"{}\", \"pointer_size_bits\": {}, \"pointer_align_abi_bytes\": {}, \"i8_align_bytes\": {}, \"i16_align_bytes\": {}, \"i32_align_bytes\": {}, \"i64_align_bytes\": {}, \"i128_align_bytes\": {}, \"f16_align_bytes\": {}, \"f32_align_bytes\": {}, \"f64_align_bytes\": {}, \"f128_align_bytes\": {}, \"aggregate_align_bytes\": {}, \"obj_size_bound_bytes\": {}}}",
            esc(&spec.llvm_target),
            esc(&spec.llvm_target),
            esc(&spec.data_layout),
            dl.endian.as_str(),
            dl.pointer_size().bits(),
            dl.pointer_align().abi.bytes(),
            dl.i8_align.bytes(),
            dl.i16_align.bytes(),
            dl.i32_align.bytes(),
            dl.i64_align.bytes(),
            dl.i128_align.bytes(),
            dl.f16_align.bytes(),
            dl.f32_align.bytes(),
            dl.f64_align.bytes(),
            dl.f128_align.bytes(),
            dl.aggregate_align.bytes(),
            dl.obj_size_bound()
        );

        let mut type_entries = Vec::new();
        for def_id in tcx.hir_crate_items(()).free_items() {
            let did = def_id.owner_id.def_id;
            if tcx.def_kind(did) == DefKind::Struct && tcx.item_name(did.to_def_id()).as_str() == "ProbeCatalog" {
                let adt = tcx.adt_def(did);
                for field in adt.all_fields() {
                    let fname = field.name.as_str();
                    let fty = tcx.type_of(field.did).instantiate_identity().skip_normalization();
                    let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(fty)).unwrap();
                    let niche_str = match layout.largest_niche {
                        Some(n) => format!("offset={}B, value={:?}, valid_range={}..={}", n.offset.bytes(), n.value, n.valid_range.start, n.valid_range.end),
                        None => "None".to_string(),
                    };
                    let entry = format!(
                        "{{\"field\": \"{}\", \"ty\": \"{}\", \"size_bytes\": {}, \"align_abi_bytes\": {}, \"unadjusted_abi_align_bytes\": {}, \"backend_repr\": \"{}\", \"fields_shape\": \"{}\", \"variants\": \"{}\", \"largest_niche\": \"{}\", \"uninhabited\": {}}}",
                        esc(fname),
                        esc(&fty.to_string()),
                        layout.size.bytes(),
                        layout.align.abi.bytes(),
                        layout.unadjusted_abi_align.bytes(),
                        esc(&fmt_backend_repr(layout.backend_repr)),
                        esc(&fmt_fields(&layout.fields)),
                        esc(&fmt_variants(&layout.variants)),
                        esc(&niche_str),
                        layout.is_uninhabited()
                    );
                    type_entries.push(entry);
                }
            }
        }
        let out = format!(
            "{{\"label\": \"{}\", \"target_data_layout\": {}, \"types\": [{}]}}",
            esc(&self.label),
            dl_json,
            type_entries.join(",\n")
        );
        std::fs::write(&self.out_path, out).unwrap();
        Compilation::Stop
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let out_idx = args.iter().position(|a| a == "--layout-out").unwrap();
    let out_path = args.remove(out_idx + 1);
    args.remove(out_idx);
    let label_idx = args.iter().position(|a| a == "--layout-label").unwrap();
    let label = args.remove(label_idx + 1);
    args.remove(label_idx);

    let mut cb = LayoutCallbacks { label, out_path };
    rustc_driver::run_compiler(&args, &mut cb);
}
