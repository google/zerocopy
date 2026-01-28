#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("./README.md")]

pub use counter::Counter;

mod counter;

#[doc(hidden)]
pub mod prelude {
    pub use super::Counter;
}
