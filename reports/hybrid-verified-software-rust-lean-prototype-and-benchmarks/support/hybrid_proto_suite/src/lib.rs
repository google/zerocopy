#![forbid(unsafe_code)]

use std::panic::{catch_unwind, RefUnwindSafe, UnwindSafe};

pub mod anneal_emit;
pub mod deflate;
pub mod sssp;

/// Capability wrapper constructible exclusively by the trusted checker path inside
/// `trust_core`. External callers and untrusted producers cannot fabricate `Certified<T>`.
pub mod trust_core {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Certified<T> {
        value: T,
    }

    impl<T> Certified<T> {
        pub(super) fn new_checked(value: T) -> Self {
            Self { value }
        }

        pub fn as_ref(&self) -> &T {
            &self.value
        }

        pub fn into_inner(self) -> T {
            self.value
        }
    }
}

pub use trust_core::Certified;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HybridTelemetry {
    pub accepts: u64,
    pub none_returns: u64,
    pub checker_rejects: u64,
    pub panics_caught: u64,
    pub fallbacks: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OriginTag {
    FastProducer,
    PortfolioAlt(usize),
    VerifiedFallback,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertifiedOutcome<T> {
    pub cert: Certified<T>,
    pub origin: OriginTag,
}

/// Core `Option<T>` hybrid combinator: runs an untrusted producer inside a panic-catching
/// boundary on an interior-immutability-free `RefUnwindSafe` input reference, checks the
/// returned `(output, witness)` pair, and mints `Certified<T>` only on checker acceptance.
pub fn verify_opt<I, T, W, P, C>(
    input: &I,
    producer: P,
    checker: C,
    telemetry: &mut HybridTelemetry,
) -> Option<Certified<T>>
where
    I: Sync + RefUnwindSafe,
    P: FnOnce(&I) -> Option<(T, W)> + UnwindSafe,
    C: FnOnce(&I, &(T, W)) -> bool,
{
    match catch_unwind(|| producer(input)) {
        Err(_) => {
            telemetry.panics_caught += 1;
            None
        }
        Ok(None) => {
            telemetry.none_returns += 1;
            None
        }
        Ok(Some(candidate)) => {
            if checker(input, &candidate) {
                telemetry.accepts += 1;
                Some(Certified::new_checked(candidate.0))
            } else {
                telemetry.checker_rejects += 1;
                None
            }
        }
    }
}

/// Total hybrid combinator with self-checked slow fallback (`Option<T>` -> `CertifiedOutcome<T>`).
/// Note that even the fallback passes through `checker` so the checker remains the sole
/// authority able to construct `Certified<T>`.
pub fn verify_or_fallback<I, T, W, P, C, F>(
    input: &I,
    producer: P,
    mut checker: C,
    fallback: F,
    telemetry: &mut HybridTelemetry,
) -> CertifiedOutcome<T>
where
    I: Sync + RefUnwindSafe,
    P: FnOnce(&I) -> Option<(T, W)> + UnwindSafe,
    C: FnMut(&I, &(T, W)) -> bool,
    F: FnOnce(&I) -> (T, W),
{
    if let Some(cert) = verify_opt(input, producer, |i, c| checker(i, c), telemetry) {
        return CertifiedOutcome {
            cert,
            origin: OriginTag::FastProducer,
        };
    }
    telemetry.fallbacks += 1;
    let fb = fallback(input);
    assert!(
        checker(input, &fb),
        "verified fallback violated checker invariant"
    );
    CertifiedOutcome {
        cert: Certified::new_checked(fb.0),
        origin: OriginTag::VerifiedFallback,
    }
}

/// Portfolio / multi-producer race (sequential deterministic hedging): tries producers in
/// order, returning the first candidate accepted by `checker` and falling back otherwise.
pub fn race_or_fallback<I, T, W, C, F>(
    input: &I,
    producers: &[&(dyn Fn(&I) -> Option<(T, W)> + Sync + RefUnwindSafe)],
    mut checker: C,
    fallback: F,
    telemetry: &mut HybridTelemetry,
) -> CertifiedOutcome<T>
where
    I: Sync + RefUnwindSafe,
    C: FnMut(&I, &(T, W)) -> bool,
    F: FnOnce(&I) -> (T, W),
{
    for (idx, prod) in producers.iter().enumerate() {
        if let Some(cert) = verify_opt(input, |i| prod(i), |i, c| checker(i, c), telemetry) {
            let origin = if idx == 0 {
                OriginTag::FastProducer
            } else {
                OriginTag::PortfolioAlt(idx)
            };
            return CertifiedOutcome { cert, origin };
        }
    }
    telemetry.fallbacks += 1;
    let fb = fallback(input);
    assert!(
        checker(input, &fb),
        "verified fallback violated checker invariant"
    );
    CertifiedOutcome {
        cert: Certified::new_checked(fb.0),
        origin: OriginTag::VerifiedFallback,
    }
}
