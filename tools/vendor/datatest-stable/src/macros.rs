// Copyright (c) The datatest-stable Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

/// `datatest-stable` test harness entry point. Should be declared in the test module.
///
/// Also, `harness` should be set to `false` for that test module in `Cargo.toml` (see [Configuring
/// a target](https://doc.rust-lang.org/cargo/reference/manifest.html#configuring-a-target)).
#[macro_export]
macro_rules! harness {
    ( $( { $($args:tt)* } ),+ $(,)* ) => {
        fn main() -> ::std::process::ExitCode {
            let mut requirements = Vec::new();
            use $crate::data_source_kinds::*;
            use $crate::test_kinds::*;

            $(
                $crate::harness_collect!(@gather_test requirements, { $($args)*, } => { });
            )+

            $crate::runner(&requirements)
        }
    };
    ( $( $name:path, $root:expr, $pattern:expr ),+ $(,)* ) => {
        // This is the old format with datatest-stable 0.2. Print a nice message
        // in this case.
        const _: () = {
            compile_error!(
concat!(r"this format is no longer supported -- please switch to specifying as:

datatest_stable::harness! {
",
    $(concat!("    { test = ", stringify!($name), ", root = ", stringify!($root), ", pattern = ", stringify!($pattern), " },\n"),)+
r"}

note: patterns are now evaluated relative to the provided root, not to the crate root
"));
        };
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! harness_collect {
    // Gather `test`
    (@gather_test
        $requirements:expr,
        // Note: here and below, rest always ends with at least 1 comma
        { test = $test:path, $($rest:tt)* } =>
        { }
    ) => {
        $crate::harness_collect!(@gather_root
            $requirements,
            { $($rest)* } =>
            { test = $test, }
        );
    };

    // `test` not found
    (@gather_test
        $requirements:expr,
        { $key:ident $($rest:tt)* } =>
        { }
    ) => {
        compile_error!(concat!("expected `test`, found `", stringify!($key), "`"));
    };

    // No remaining arguments
    (@gather_test
        $requirements:expr,
        { $(,)* } =>
        { }
    ) => {
        compile_error!("expected `test`, but ran out of arguments");
    };

    // Something that isn't an identifier
    (@gather_test
        $requirements:expr,
        { $($rest:tt)* } =>
        { }
    ) => {
        compile_error!(concat!("expected `test`, found non-identifier token: (rest: ", stringify!($($rest)*), ")"));
    };

    // Gather `root`
    (@gather_root
        $requirements:expr,
        { root = $root:expr, $($rest:tt)* } =>
        { $($collected:tt)* }
    ) => {
        $crate::harness_collect!(@gather_pattern
            $requirements,
            { $($rest)* } =>
            { $($collected)* root = $root, }
        );
    };

    // `root` not found
    (@gather_root
        $requirements:expr,
        { $key:ident $($rest:tt)* } =>
        { $($collected:tt)* }
    ) => {
        compile_error!(concat!("expected `root`, found `", stringify!($key), "`"));
    };

    // No remaining arguments
    (@gather_root
        $requirements:expr,
        { $(,)* } =>
        { $($collected:tt)* }
    ) => {
        compile_error!(concat!("expected `root`, but ran out of arguments (collected: ", stringify!($($collected)*), ")"));
    };

    // Something that isn't an identifier
    (@gather_root
        $requirements:expr,
        { $($rest:tt)* } =>
        { $($collected:tt)* }
    ) => {
        compile_error!(concat!("expected `root`, found non-identifier token (rest: ", stringify!($($rest)*), ")"));
    };

    // Gather pattern
    (@gather_pattern
        $requirements:expr,
        { pattern = $pattern:expr, $($rest:tt)* } =>
        { $($collected:tt)* }
    ) => {
        $crate::harness_collect!(@finish
            $requirements,
            { $($rest)* } =>
            { $($collected)* pattern = $pattern, }
        );
    };

    // `pattern` not found
    (@gather_pattern
        $requirements:expr,
        { $key:ident $($rest:tt)* } =>
        { $($collected:tt)* }
    ) => {
        compile_error!(concat!("expected `pattern`, found `", stringify!($key), "`"));
    };

    // `pattern` not found: no remaining arguments
    (@gather_pattern
        $requirements:expr,
        { $(,)* } =>
        { $($collected:tt)* }
    ) => {
        $crate::harness_collect!(@finish
            $requirements,
            { } =>
            { $($collected)* pattern = ".*", }
        );
    };

    // Something that isn't an identifier
    (@gather_pattern
        $requirements:expr,
        { $($rest:tt)* } =>
        { $($collected:tt)* }
    ) => {
        compile_error!(concat!("expected `pattern`, found non-identifier token (rest: ", stringify!($($rest)*), ")"));
    };

    // Finish - no more arguments allowed
    (@finish
        $requirements:expr,
        { $(,)* } =>
        { test = $test:path, root = $root:expr, pattern = $pattern:expr, }
    ) => {
        $requirements.push(
            $crate::Requirements::new(
                $test.kind().resolve($test),
                stringify!($test).to_string(),
                $root.resolve_data_source(),
                $pattern.to_string()
            )
        );
    };

    // Finish - unexpected extra arguments
    (@finish
        $requirements:expr,
        { $($unexpected:tt)+ } =>
        { $($collected:tt)* }
    ) => {
        compile_error!(concat!("unexpected extra arguments: ", stringify!($($unexpected)+)));
    };
}
