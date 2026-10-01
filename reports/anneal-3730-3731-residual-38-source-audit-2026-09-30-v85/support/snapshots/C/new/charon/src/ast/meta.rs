//! Meta information about programs (spans, etc.).
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::EnumIsA;
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

use super::from_rustc::LangItem;

pub mod attrs;
pub mod names;
pub mod spans;

pub use attrs::*;
pub use names::*;
pub use spans::*;

/// How much to translate for a given item.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[derive(EnumIsA)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub enum ItemOpacity {
    /// Translate the item fully.
    Transparent,
    /// Translate the item depending on the normal rust visibility of its contents: for types, we
    /// translate fully if it is a struct with public fields or an enum; for other items this is
    /// equivalent to `Opaque`.
    Foreign,
    /// Translate the item name and signature, but not its contents. For function and globals, this
    /// means we don't translate the body (the code); for ADTs, this means we don't translate the
    /// fields/variants. For traits and trait impls, this doesn't change anything. For modules,
    /// this means we don't explore its contents (we still translate any of its items mentioned
    /// from somewhere else).
    ///
    /// This can happen either if the item was annotated with `#[charon::opaque]` or if it was
    /// declared opaque via a command-line argument.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("ItemOpaque"))]
    Opaque,
    /// Translate nothing of this item. The corresponding map will not have an entry for the
    /// `ItemId`. Useful when even the signature of the item causes errors.
    Invisible,
}

/// Meta information about an item (function, trait decl, trait impl, type decl, global).
#[derive(Debug, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(stateless)]
pub struct ItemMeta {
    #[serde_state(stateful)]
    pub name: Name,
    pub span: Span,
    /// The source code that corresponds to this item.
    pub source_text: Option<String>,
    /// Attributes and visibility.
    pub attr_info: AttrInfo,
    /// `true` if the type decl is a local type decl, `false` if it comes from an external crate.
    pub is_local: bool,
    /// Whether this item was selected as a starting point for translation (using `--start-from`,
    /// or by default all the top-level items in the main crate).
    pub started_from: bool,
    /// Whether this item is considered opaque. For function and globals, this means we don't
    /// translate the body (the code); for ADTs, this means we don't translate the fields/variants.
    /// For traits and trait impls, this doesn't change anything. For modules, this means we don't
    /// explore its contents (we still translate any of its items mentioned from somewhere else).
    ///
    /// This can happen either if the item was annotated with `#[charon::opaque]` or if it was
    /// declared opaque via a command-line argument.
    pub opacity: ItemOpacity,
    /// If the item is a rustc lang item, record which one it is.
    pub lang_item: Option<LangItem>,
    /// If the item is a rustc diagnostic item, record its internal identifier.
    pub diagnostic_item: Option<String>,
    /// Whether an error occurred while translating this item.
    pub has_errors: bool,
}

impl ItemOpacity {
    pub fn with_content_visibility(self, contents_are_public: bool) -> Self {
        use ItemOpacity::*;
        match self {
            Invisible => Invisible,
            Transparent => Transparent,
            Foreign if contents_are_public => Transparent,
            Foreign => Opaque,
            Opaque => Opaque,
        }
    }

    pub fn with_private_contents(self) -> Self {
        self.with_content_visibility(false)
    }
}

impl ItemMeta {
    pub fn renamed_name(&self) -> Name {
        let mut name = self.name.clone();
        if let Some(rename) = self.attr_info.rename.clone() {
            *name.name.last_mut().unwrap() = PathElem::Ident(rename, Disambiguator::new(0));
        }
        name
    }

    pub fn dummy_public(span: Span, name: Name, is_local: bool, opacity: ItemOpacity) -> Self {
        ItemMeta {
            name,
            span,
            source_text: None,
            attr_info: AttrInfo::dummy_public(),
            is_local,
            started_from: false,
            opacity,
            lang_item: None,
            diagnostic_item: None,
            has_errors: false,
        }
    }
}
