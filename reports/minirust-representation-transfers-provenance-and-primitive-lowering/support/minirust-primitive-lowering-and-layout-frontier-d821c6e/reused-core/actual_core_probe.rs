// Owned probe through the actual generated MiniRust core API.
// Host Rust is safe. The core programs may deliberately return semantic UB.
use miniutil::*;
use miniutil::build::*;
use miniutil::run::*;
use minirust_rs::libspecr::prelude::*;
use minirust_rs::lang::*;
use minirust_rs::prelude::*;

fn specimen(coherent: bool, wanted: u8) -> Program {
    let payload = tuple_ty(&[], size(1), align(1));
    let int_ty = IntType { signed: Signedness::Unsigned, size: size(1) };
    let disc = if coherent {
        discriminator_branch::<u8>(offset(0), discriminator_known(0),
            &[((1u8,2u8),discriminator_known(1))])
    } else { discriminator_known(0) };
    let ty = enum_ty::<u8>(&[
        (0,enum_variant(payload,&[(offset(0),(int_ty,0.into()))])),
        (1,enum_variant(payload,&[(offset(0),(int_ty,1.into()))])),
    ],disc,size(1),align(1));
    let blocks = [
        block!(
            storage_live(0),
            storage_live(1),
            assign(local(0),variant(1,tuple(&[],payload),ty)),
            assign(local(1),load(local(0))),
            switch_int(get_discriminant(local(1)),&[(wanted,1)],2)
        ),
        block!(exit()),
        block!(unreachable()),
    ];
    program(&[function(Ret::No,0,&[ty,ty],&blocks)])
}
fn wide_union(short_chunks: bool) -> Program {
    // miniutil's DefaultTarget is the modeled x86_64 target: pointer words are8B.
    let wide = <*const [u8]>::get_type();
    let union = Type::Union {
        fields: [(size(0),wide)].into_iter().collect(),
        size: size(16), align: align(8),
        chunks: [(size(0),size(if short_chunks {8} else {16}))].into_iter().collect(),
    };
    let locals = [<[u8;3]>::get_type(),wide,union,wide];
    let blocks = [
        block!(
            storage_live(0),storage_live(1),storage_live(2),storage_live(3),
            assign(local(0),array(&[const_int(1u8),const_int(2u8),const_int(3u8)],u8::get_type())),
            assign(local(1),construct_wide_pointer(
                addr_of(local(0),<*const u8>::get_type()),const_int(3usize),wide)),
            assign(local(2),transmute(load(local(1)),union)),
            assign(local(3),transmute(load(local(2)),wide)),
            switch_int(get_metadata(load(local(3))),&[(3usize,1)],2)
        ),
        block!(exit()),block!(unreachable()),
    ];
    program(&[function(Ret::No,0,&locals,&blocks)])
}
fn main() {
    for n in [1u8,2u8] {
        let p=small_program(&[bool::get_type()],&[
            storage_live(0),
            assign(local(0),transmute(const_int(n),bool::get_type())),
        ]);
        println!("CASE bool_transmute_{n}");
        println!("OUTCOME {:?}",run_program::<BasicMem>(p));
    }
    let p=small_program(&[u8::get_type()],&[
        storage_live(0),
        assign(local(0),add_unchecked(const_int(255u8),const_int(1u8))),
    ]);
    println!("CASE unchecked_u8_overflow");
    println!("OUTCOME {:?}",run_program::<BasicMem>(p));
    for (name,coherent,wanted) in [
        ("incoherent_known0_observes0",false,0),
        ("coherent_tag1_observes1",true,1),
        ("wrong_expected1_negative_control",false,1),
    ] {
        let p=specimen(coherent,wanted);
        println!("CASE {name}");
        println!("OUTCOME {:?}",run_program::<BasicMem>(p));
    }
    for short in [false,true] {
        println!("CASE wide_pointer_union_{}_chunk",if short {"oneword"} else {"twoword"});
        println!("OUTCOME {:?}",run_program::<BasicMem>(wide_union(short)));
    }
}
