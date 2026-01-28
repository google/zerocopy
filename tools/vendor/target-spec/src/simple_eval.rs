// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, TargetSpec,
    platform::{Platform, TargetFeatures},
};

/// Evaluates the given spec against the provided target and returns `Some(true)` on a successful
/// match, and `Some(false)` on a failing match.
///
/// This defaults to treating target features as unknown, and returns `None` if the overall result
/// is unknown.
///
/// For more advanced uses, see [`TargetSpec::eval`].
///
/// For more information, see the crate-level documentation.
pub fn eval(spec_or_triple: &str, platform: &str) -> Result<Option<bool>, Error> {
    let target_spec = spec_or_triple.parse::<TargetSpec>()?;
    let platform = Platform::new(platform.to_owned(), TargetFeatures::Unknown)?;
    Ok(target_spec.eval(&platform))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_windows() {
        assert_eq!(
            eval("cfg(windows)", "x86_64-pc-windows-msvc").unwrap(),
            Some(true),
        );
    }

    #[test]
    fn test_not_target_os() {
        assert_eq!(
            eval(
                "cfg(not(target_os = \"windows\"))",
                "x86_64-unknown-linux-gnu"
            )
            .unwrap(),
            Some(true),
        );
    }

    #[test]
    fn test_not_target_os_false() {
        assert_eq!(
            eval(
                "cfg(not(target_os = \"windows\"))",
                "x86_64-pc-windows-msvc"
            )
            .unwrap(),
            Some(false),
        );
    }

    #[test]
    fn test_exact_triple() {
        assert_eq!(
            eval("x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu").unwrap(),
            Some(true),
        );
    }

    #[test]
    fn test_redox() {
        assert_eq!(
            eval(
                "cfg(any(unix, target_os = \"redox\"))",
                "x86_64-unknown-linux-gnu"
            )
            .unwrap(),
            Some(true),
        );
    }

    #[test]
    fn test_bogus_families() {
        // Known bogus families.
        for family in &["test", "debug_assertions", "proc_macro"] {
            let cfg = format!("cfg({family})");
            let cfg_not = format!("cfg(not({family}))");
            assert_eq!(eval(&cfg, "x86_64-unknown-linux-gnu").unwrap(), Some(false));
            assert_eq!(
                eval(&cfg_not, "x86_64-unknown-linux-gnu").unwrap(),
                Some(true)
            );
        }

        // Unknown bogus families.
        let platform = Platform::new("x86_64-unknown-linux-gnu", TargetFeatures::Unknown).unwrap();
        let mut platform_with_flags = platform.clone();
        platform_with_flags.add_flags(["foo", "bar"].iter().copied());

        for family in &["foo", "bar"] {
            let cfg = format!("cfg({family})");
            let cfg_not = format!("cfg(not({family}))");

            // eval always means flags are evaluated to false.
            assert_eq!(eval(&cfg, "x86_64-unknown-linux-gnu").unwrap(), Some(false));
            assert_eq!(
                eval(&cfg_not, "x86_64-unknown-linux-gnu").unwrap(),
                Some(true)
            );

            let spec: TargetSpec = cfg.parse().unwrap();
            let spec_not: TargetSpec = cfg_not.parse().unwrap();

            // flag missing means false.
            assert_eq!(spec.eval(&platform), Some(false));
            assert_eq!(spec_not.eval(&platform), Some(true));

            // flag present means true.
            assert_eq!(spec.eval(&platform_with_flags), Some(true));
            assert_eq!(spec_not.eval(&platform_with_flags), Some(false));
        }

        for family in &["baz", "nonsense"] {
            let cfg = format!("cfg({family})");
            let cfg_not = format!("cfg(not({family}))");

            // eval always means flags are evaluated to false.
            assert_eq!(eval(&cfg, "x86_64-unknown-linux-gnu").unwrap(), Some(false));
            assert_eq!(
                eval(&cfg_not, "x86_64-unknown-linux-gnu").unwrap(),
                Some(true)
            );

            let spec: TargetSpec = cfg.parse().unwrap();
            let spec_not: TargetSpec = cfg_not.parse().unwrap();

            // flag missing means false.
            assert_eq!(spec.eval(&platform), Some(false));
            assert_eq!(spec_not.eval(&platform), Some(true));

            // flag still missing means false.
            assert_eq!(spec.eval(&platform_with_flags), Some(false));
            assert_eq!(spec_not.eval(&platform_with_flags), Some(true));
        }
    }

    #[test]
    fn test_target_feature() {
        // target features are unknown by default.
        assert_eq!(
            eval("cfg(target_feature = \"sse\")", "x86_64-unknown-linux-gnu").unwrap(),
            None,
        );
        assert_eq!(
            eval(
                "cfg(target_feature = \"atomics\")",
                "x86_64-unknown-linux-gnu",
            )
            .unwrap(),
            None,
        );
        assert_eq!(
            eval(
                "cfg(not(target_feature = \"fxsr\"))",
                "x86_64-unknown-linux-gnu",
            )
            .unwrap(),
            None,
        );

        fn eval_unknown(spec: &str, platform: &str) -> Option<bool> {
            let platform = Platform::new(
                platform.to_owned(),
                TargetFeatures::features(["sse", "sse2"].iter().copied()),
            )
            .expect("platform should be found");
            let spec: TargetSpec = spec.parse().unwrap();
            spec.eval(&platform)
        }

        assert_eq!(
            eval_unknown("cfg(target_feature = \"sse\")", "x86_64-unknown-linux-gnu"),
            Some(true),
        );
        assert_eq!(
            eval_unknown(
                "cfg(not(target_feature = \"sse\"))",
                "x86_64-unknown-linux-gnu",
            ),
            Some(false),
        );
        assert_eq!(
            eval_unknown("cfg(target_feature = \"fxsr\")", "x86_64-unknown-linux-gnu"),
            Some(false),
        );
        assert_eq!(
            eval_unknown(
                "cfg(not(target_feature = \"fxsr\"))",
                "x86_64-unknown-linux-gnu",
            ),
            Some(true),
        );

        fn eval_all(spec: &str, platform: &str) -> Option<bool> {
            let platform = Platform::new(platform.to_owned(), TargetFeatures::All)
                .expect("platform should be found");
            let spec: TargetSpec = spec.parse().unwrap();
            spec.eval(&platform)
        }

        assert_eq!(
            eval_all("cfg(target_feature = \"sse\")", "x86_64-unknown-linux-gnu"),
            Some(true),
        );
        assert_eq!(
            eval_all(
                "cfg(not(target_feature = \"sse\"))",
                "x86_64-unknown-linux-gnu",
            ),
            Some(false),
        );
        assert_eq!(
            eval_all("cfg(target_feature = \"fxsr\")", "x86_64-unknown-linux-gnu"),
            Some(true),
        );
        assert_eq!(
            eval_all(
                "cfg(not(target_feature = \"fxsr\"))",
                "x86_64-unknown-linux-gnu",
            ),
            Some(false),
        );
    }
}
