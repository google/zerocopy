#![no_std]

// The tripwire is triggered.
#[cfg(feature = "nextest")]
compile_error!(
    "Nextest does not support being installed without --locked. To install nextest from source, run:

cargo install --locked cargo-nextest

For more, see https://nexte.st/docs/installation/from-source/.");

#[cfg(not(feature = "nextest"))]
compile_error!(
    "This binary does not support being installed without --locked. To install, run:

cargo install --locked <binary>"
);
