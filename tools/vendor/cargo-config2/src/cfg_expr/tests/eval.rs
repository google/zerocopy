// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::{cfg_expr::expr::Expression, resolve::CfgMap};

#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
fn target_family() {
    let matches_any_family =
        Expression::parse("any(unix, target_family = \"windows\", target_family = \"wasm\")")
            .unwrap();
    let impossible = Expression::parse("all(windows, target_family = \"unix\")").unwrap();

    let mut map = CfgMap::default();
    for target in [
        "aarch64-apple-darwin",
        "x86_64-pc-windows-msvc",
        "wasm32-unknown-unknown",
        "thumbv7m-none-eabi",
    ] {
        let t = map.eval_cfg(&matches_any_family, &target.into(), || cmd!("rustc")).unwrap();
        if target.contains("-none") {
            assert!(!t, "{target}");
        } else {
            assert!(t, "{target}");
        }
        assert!(!map.eval_cfg(&impossible, &target.into(), || cmd!("rustc")).unwrap());
    }
}

#[test]
fn tiny() {
    assert!(Expression::parse("all()").unwrap().eval(|_| false));
    assert!(!Expression::parse("any()").unwrap().eval(|_| true));
    assert!(!Expression::parse("not(all())").unwrap().eval(|_| false));
    assert!(Expression::parse("not(any())").unwrap().eval(|_| true));
    assert!(Expression::parse("all(not(blah))").unwrap().eval(|_| false));
    assert!(!Expression::parse("any(not(blah))").unwrap().eval(|_| true));
}

#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
fn very_specific() {
    let specific = Expression::parse(
        r#"all(
            target_os = "windows",
            target_arch = "x86",
            windows,
            target_env = "msvc",
            target_feature = "fxsr",
            target_feature = "sse",
            target_feature = "sse2",
            target_pointer_width = "32",
            target_endian = "little",
            not(target_vendor = "uwp"),
            target_has_atomic = "8",
            target_has_atomic = "16",
            target_has_atomic = "32",
            target_has_atomic = "64",
            not(target_has_atomic = "128"),
            target_has_atomic = "ptr",
            panic = "unwind",
            not(panic = "abort"),
        )"#,
    )
    .unwrap();

    let mut map = CfgMap::default();
    for target in ["i686-pc-windows-msvc", "i686-pc-windows-gnu"] {
        let t = map.eval_cfg(&specific, &target.into(), || cmd!("rustc")).unwrap();
        assert_eq!(
            target == "i686-pc-windows-msvc",
            t,
            "expected true for i686-pc-windows-msvc, but got true for {target}",
        );
    }

    // for target in all {
    //     let expr = format!(
    //         r#"cfg(
    //         all(
    //             target_arch = "{}",
    //             {}
    //             {}
    //             target_env = "{}"
    //         )
    //     )"#,
    //         target.arch.0,
    //         if let Some(v) = &target.vendor {
    //             format!(r#"target_vendor = "{}","#, v.0)
    //         } else {
    //             "".to_owned()
    //         },
    //         if let Some(v) = &target.os {
    //             format!(r#"target_os = "{}","#, v.0)
    //         } else {
    //             "".to_owned()
    //         },
    //         target.env.as_ref().map_or("", |e| e.as_str()),
    //     );

    //     let specific = Expression::parse(&expr).unwrap();

    //     let t = Target::make(target.triple.as_str());
    //     assert!(
    //         specific.eval(|pred| {
    //             if target.triple.as_str() == "mips64-openwrt-linux-musl" {
    //                 if let Predicate::Target(TargetPredicate::Vendor(vendor)) = pred {
    //                     // This is a special predicate that doesn't follow the usual rules for
    //                     // target-lexicon.
    //                     return t.builtin.matches(&TargetPredicate::Vendor(vendor.clone()));
    //                 }
    //             }
    //             tg_match!(pred, t)
    //         }),
    //         "failed expression '{}' for {:#?}",
    //         expr,
    //         t.builtin,
    //     );
    // }
}

#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
fn complex() {
    let complex = Expression::parse(r#"cfg(all(unix, not(any(target_os="macos", target_os="android", target_os="emscripten"))))"#).unwrap();

    let mut map = CfgMap::default();

    // Should match linuxes
    assert!(map.eval_cfg(&complex, &"x86_64-unknown-linux-gnu".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"x86_64-unknown-linux-musl".into(), || cmd!("rustc")).unwrap());

    // Should *not* match windows or mac or android
    assert!(!map.eval_cfg(&complex, &"x86_64-pc-windows-msvc".into(), || cmd!("rustc")).unwrap());
    assert!(!map.eval_cfg(&complex, &"x86_64-apple-darwin".into(), || cmd!("rustc")).unwrap());
    assert!(!map.eval_cfg(&complex, &"aarch64-linux-android".into(), || cmd!("rustc")).unwrap());

    let complex =
        Expression::parse(r#"all(not(target_os = "ios"), not(target_os = "android"))"#).unwrap();

    assert!(map.eval_cfg(&complex, &"x86_64-unknown-linux-gnu".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"x86_64-unknown-linux-musl".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"x86_64-pc-windows-msvc".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"x86_64-apple-darwin".into(), || cmd!("rustc")).unwrap());
    assert!(!map.eval_cfg(&complex, &"aarch64-linux-android".into(), || cmd!("rustc")).unwrap());

    let complex = Expression::parse(r#"all(any(unix, target_arch="x86"), not(any(target_os="android", target_os="emscripten")))"#).unwrap();

    // Should match linuxes and mac
    assert!(map.eval_cfg(&complex, &"x86_64-unknown-linux-gnu".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"x86_64-unknown-linux-musl".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"x86_64-apple-darwin".into(), || cmd!("rustc")).unwrap());

    // Should *not* match x86_64 windows or android
    assert!(!map.eval_cfg(&complex, &"x86_64-pc-windows-msvc".into(), || cmd!("rustc")).unwrap());
    assert!(!map.eval_cfg(&complex, &"aarch64-linux-android".into(), || cmd!("rustc")).unwrap());

    // Ensure that target_os = "none" matches against Os == None.
    let complex = Expression::parse(r#"all(target_os="none")"#).unwrap();
    assert!(!map.eval_cfg(&complex, &"x86_64-unknown-linux-gnu".into(), || cmd!("rustc")).unwrap());
    assert!(map.eval_cfg(&complex, &"armebv7r-none-eabi".into(), || cmd!("rustc")).unwrap());
}

// #[test]
// fn unstable_target_abi() {
//     let linux_gnu = Target::make("x86_64-unknown-linux-gnu");
//     let linux_musl = Target::make("x86_64-unknown-linux-musl");
//     let windows_msvc = Target::make("x86_64-pc-windows-msvc");
//     let mac = Target::make("x86_64-apple-darwin");
//     let android = Target::make("aarch64-linux-android");

//     let target_with_abi_that_matches = cfg_expr::targets::TargetInfo {
//         triple: cfg_expr::targets::Triple::new_const("aarch64-apple-darwin"),
//         os: None,
//         abi: Some(cfg_expr::targets::Abi::new_const("eabihf")),
//         arch: cfg_expr::targets::Arch::aarch64,
//         env: None,
//         vendor: None,
//         families: cfg_expr::targets::Families::unix,
//         pointer_width: 64,
//         endian: cfg_expr::targets::Endian::little,
//         has_atomics: cfg_expr::targets::HasAtomics::atomic_8_16_32_64_128_ptr,
//         panic: cfg_expr::targets::Panic::unwind,
//     };

//     let target_with_abi_that_does_not_match = cfg_expr::targets::TargetInfo {
//         abi: Some(cfg_expr::targets::Abi::new_const("ilp32")),
//         ..target_with_abi_that_matches.clone()
//     };

//     let abi_pred =
//         Expression::parse(r#"cfg(any(target_arch = "wasm32", target_abi = "eabihf"))"#).unwrap();

//     // Should match a specified target_abi that's the same
//     assert!(abi_pred.eval(|pred| {
//         match pred {
//             Predicate::Target(tp) => tp.matches(&target_with_abi_that_matches),
//             _ => false,
//         }
//     }));

//     // Should *not* match a specified target_abi that isn't the same
//     assert!(!abi_pred.eval(|pred| {
//         match pred {
//             Predicate::Target(tp) => tp.matches(&target_with_abi_that_does_not_match),
//             _ => false,
//         }
//     }));

//     // Should *not* match any builtins at this point because target_abi isn't stable
//     assert!(!abi_pred.eval(|pred| tg_match!(pred, linux_gnu)));
//     assert!(!abi_pred.eval(|pred| tg_match!(pred, linux_musl)));
//     assert!(!abi_pred.eval(|pred| tg_match!(pred, mac)));
//     assert!(!abi_pred.eval(|pred| tg_match!(pred, windows_msvc)));
//     assert!(!abi_pred.eval(|pred| tg_match!(pred, android)));
// }

#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
fn wasm_family() {
    let wasm = Expression::parse(r#"cfg(target_family = "wasm")"#).unwrap();

    let mut map = CfgMap::default();

    // All of the above targets match.
    for target in [
        "wasm32-unknown-unknown",
        "wasm32-unknown-emscripten",
        "wasm32-wasip1",
        "wasm64-unknown-unknown",
    ] {
        assert!(map.eval_cfg(&wasm, &target.into(), || cmd!("rustc")).unwrap(), "{target}");
    }
}
