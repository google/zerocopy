//! User-visible names of items.
use crate::ast::*;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use itertools::Itertools;
use macros::{EnumAsGetters, EnumIsA};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

generate_index_type!(Disambiguator);

// Some known names we may refer to.
/// We treat this one specially in the `inline_local_panic_functions` pass. See there for details.
pub static EXPLICIT_PANIC_NAME: &[&str] = &["core", "panicking", "panic_explicit"];
pub static BOX_ASSUME_INIT_INTO_VEC_UNSAFE: &str = "box_assume_init_into_vec_unsafe";
pub static BOX_NEW: &str = "alloc::boxed::Box::new";
pub static BOX_WRITE: &str = "alloc::boxed::Box::write";
pub static BOX_WRITE_PATTERN: &str = "alloc::boxed::_::write"; // `_` matches an impl block

/// See the comments for [Name]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Pe"))]
pub enum PathElem {
    #[serde_state(stateless)]
    Ident(String, Disambiguator),
    Impl(ImplElem),
    /// This item was obtained by instantiating its parent with the given args. The binder binds
    /// the parameters of the new items. If the binder binds nothing then this is a
    /// monomorphization.
    Instantiated(Box<Binder<GenericArgs>>),
    /// This item is only available on the given target. Only appears in multi-target mode.
    #[serde_state(stateless)]
    Target(TargetTriple),
    /// A path element that doesn't come from the source code: either a builtin type such as
    /// tuples, or an item that has no name of its own such as a closure or a vtable.
    #[serde_state(stateless)]
    Builtin(BuiltinPathElem, Disambiguator),
}

/// Used for builtin items, rather than hardcoding these as strings.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(Serialize, Deserialize)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Pe"))]
pub enum BuiltinPathElem {
    /// The tuple of the given arity.
    Tuple(usize),
    /// `str`, which is a struct containing a `[u8]` the standard library expects
    /// to be valid UTF-8.
    Str,
    /// A closure.
    Closure,
    /// A `use` declaration.
    Use,
    /// An anonymous constant.
    AnonConst,
    /// A constant that rustc promoted out of a body.
    PromotedConst,
    /// The function item we generate for a closure that is cast to a function pointer.
    ClosureAsFn,
    /// The method we add to the `Destruct` trait to hold the drop glue.
    DropGlue,
    /// The vtable struct of a trait, or the vtable global of a trait impl.
    VTable,
    /// The version of a method that is stored in a vtable.
    VTableMethod,
    /// The `drop_in_place` shim stored in a vtable.
    VTableDropShim,
}

/// There are two kinds of `impl` blocks:
/// - impl blocks linked to a type ("inherent" impl blocks following Rust terminology):
///   ```text
///   impl<T> List<T> { ...}
///   ```
/// - trait impl blocks:
///   ```text
///   impl<T> PartialEq for List<T> { ...}
///   ```
/// We distinguish the two.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("ImplElem"))]
pub enum ImplElem {
    Ty(Box<Binder<Ty>>),
    Trait(TraitImplId),
}

/// An item name/path
///
/// A name really is a list of strings. However, we sometimes need to
/// introduce unique indices to disambiguate. This mostly happens because
/// of "impl" blocks:
///   ```text
///   impl<T> List<T> {
///     ...
///   }
///   ```
///
/// A type in Rust can have several "impl" blocks, and  those blocks can
/// contain items with similar names. For this reason, we need to disambiguate
/// them with unique indices. Rustc calls those "disambiguators". In rustc, this
/// gives names like this:
/// - `betree_main::betree::NodeIdCounter{impl#0}::new`
/// - note that impl blocks can be nested, and macros sometimes generate
///   weird names (which require disambiguation):
///   `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`
///
/// Finally, the paths used by rustc are a lot more precise and explicit than
/// those we expose in LLBC: for instance, every identifier belongs to a specific
/// namespace (value namespace, type namespace, etc.), and is coupled with a
/// disambiguator.
///
/// On our side, we want to stay high-level and simple: we use string identifiers
/// as much as possible, insert disambiguators only when necessary (for instance
/// when we find an "impl" block or when two loaded crates have the same name)
/// and check that the disambiguator is useless in the other situations (i.e.,
/// the disambiguator is always equal to 0).
///
/// Moreover, the items are uniquely disambiguated by their (integer) ids
/// (`TypeDeclId`, etc.), and when extracting the code we have to deal with
/// name clashes anyway. Still, we might want to be more precise in the future.
///
/// Also note that the first path element in the name is always the crate name.
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde(transparent)]
#[cfg_attr(feature = "charon_on_charon", charon::transparent)]
pub struct Name {
    pub name: Vec<PathElem>,
}

impl PathElem {
    fn equals_ident(&self, id: &str) -> bool {
        match self {
            PathElem::Ident(s, d) => s == id && d.is_zero(),
            _ => false,
        }
    }

    pub fn as_monomorphized(&self) -> Option<&GenericArgs> {
        let binder = self.as_instantiated()?;
        binder.params.is_empty().then_some(&binder.skip_binder)
    }
    pub fn as_monomorphized_mut(&mut self) -> Option<&mut GenericArgs> {
        let binder = self.as_instantiated_mut()?;
        binder.params.is_empty().then_some(&mut binder.skip_binder)
    }
    pub fn is_monomorphized(&self) -> bool {
        self.as_monomorphized().is_some()
    }
}

impl Name {
    /// Convert a path like `["std", "alloc", "Box"]` to a name. Needed on occasion when crafting
    /// names that were not present in the original code.
    pub fn from_path(path: &[&str]) -> Name {
        Name {
            name: path
                .iter()
                .map(|elem| PathElem::Ident(elem.to_string(), Disambiguator::ZERO))
                .collect(),
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.name.len()
    }

    /// If this item comes from monomorphization, return the arguments used.
    pub fn mono_args(&self) -> Option<&GenericArgs> {
        self.name.last()?.as_monomorphized()
    }
    /// If this item comes from monomorphization, return the arguments used.
    pub fn mono_args_mut(&mut self) -> Option<&mut GenericArgs> {
        self.name.last_mut()?.as_monomorphized_mut()
    }

    /// Strip the trailing `PathElem::Target` from a name, if any.
    pub fn strip_target_suffix(&self) -> Option<(Name, TargetTriple)> {
        match self.name.last() {
            Some(PathElem::Target(target)) => {
                let target = target.clone();
                let mut base = self.clone();
                base.name.pop();
                Some((base, target))
            }
            _ => None,
        }
    }

    /// Returns this name with the `PathElem::Instantiated` part removed, if it has one.
    pub fn as_slice_uninstantiated(&self) -> &[PathElem] {
        match self.name.as_slice() {
            [name @ .., PathElem::Instantiated(_)] => name,
            name => name,
        }
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    ///
    /// `equal`: if `true`, check that the name is equal to the ref. If `false`:
    /// only check if the ref is a prefix of the name.
    pub fn compare_with_ref_name(&self, equal: bool, ref_name: &[&str]) -> bool {
        let name: Vec<&PathElem> = self.name.iter().filter(|e| e.is_ident()).collect();

        if name.len() < ref_name.len() || (equal && name.len() != ref_name.len()) {
            return false;
        }

        for i in 0..ref_name.len() {
            if !name[i].equals_ident(ref_name[i]) {
                return false;
            }
        }
        true
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(true, ref_name)
    }

    /// Created an instantiated version of this name by putting a `PathElem::Instantiated` last. If
    /// the item was already instantiated, this merges the two instantiations.
    pub fn instantiate(mut self, binder: Binder<GenericArgs>) -> Self {
        if let [.., PathElem::Instantiated(x)] = self.name.as_mut_slice() {
            // Put the new args in place; the params are what we want but the args are wrong.
            let old_args = std::mem::replace(x.as_mut(), binder);
            // Apply the new args to the old binder to get correct args.
            x.skip_binder = old_args.apply(&x.skip_binder);
        } else {
            self.name.push(PathElem::Instantiated(Box::new(binder)));
        }
        self
    }

    /// Whether this names one of the items Rust builds into the language (tuples, `str`, arrays,
    /// slices) or an item we generate for one, such as its drop glue. They belong to no crate, so
    /// their name starts either with the builtin itself or with the `impl` block we generated for them.
    pub fn is_builtin(&self) -> bool {
        matches!(
            self.name.first(),
            Some(PathElem::Builtin(..) | PathElem::Impl(_))
        )
    }

    /// Get the last identifier of the name, if any. This is useful for error messages and such.
    /// Returns `None` if the name is empty or if the last element has no identifier to give.
    pub fn short_str(&self) -> Option<&str> {
        match self.name.last()? {
            PathElem::Builtin(builtin, _) => Some(builtin.ident()),
            PathElem::Ident(str, _) => Some(str),
            _ => None,
        }
    }

    /// `Name` is a complex datastructure; to inspect it we serialize it a little bit.
    /// This must only be used for debug printing; it is not reliable or exact.
    pub fn debug_repr(&self, crate_data: &TranslatedCrate) -> String {
        // Small helper
        let trait_name = |impl_id: TraitImplId| {
            crate_data
                .trait_impls
                .get(impl_id)
                .and_then(|timpl| crate_data.trait_decls.get(timpl.impl_trait.id))
                .and_then(|tr| tr.item_meta.name.name.last())
                .and_then(|p| p.as_ident())
                .map(|(name, _)| name)
        };

        self.name
            .iter()
            .map(|path_elem| match path_elem {
                PathElem::Ident(i, _) => i.clone(),
                PathElem::Impl(elem) => match elem {
                    ImplElem::Trait(impl_id) => match trait_name(*impl_id) {
                        None => format!("<trait impl#{impl_id}>"),
                        Some(name) => format!("<impl {name} for ??>"),
                    },
                    ImplElem::Ty(..) => "<inherent impl>".to_string(),
                },
                PathElem::Instantiated(..) => "<mono>".to_string(),
                PathElem::Target(target) => target.clone(),
                PathElem::Builtin(builtin, _) => format!("<{}>", builtin.ident()),
            })
            .join("::")
    }
}

impl BuiltinPathElem {
    /// If this builtin name is also how Rust refers to the item, in which case we don't
    /// need to put braces around the name, as it is part of the actual path of the item.
    pub fn is_rust_name(self) -> bool {
        matches!(
            self,
            BuiltinPathElem::Str | BuiltinPathElem::Tuple(_) | BuiltinPathElem::DropGlue
        )
    }

    /// The identifier we use to refer to this element.
    pub fn ident(self) -> &'static str {
        match self {
            BuiltinPathElem::Tuple(0) => "unit",
            BuiltinPathElem::Tuple(_) => "tuple",
            BuiltinPathElem::Str => "str",
            BuiltinPathElem::Closure => "closure",
            BuiltinPathElem::Use => "use",
            BuiltinPathElem::AnonConst => "const",
            BuiltinPathElem::PromotedConst => "promoted_const",
            BuiltinPathElem::ClosureAsFn => "as_fn",
            BuiltinPathElem::DropGlue => "drop_glue",
            BuiltinPathElem::VTable => "vtable",
            BuiltinPathElem::VTableMethod => "vtable_method",
            BuiltinPathElem::VTableDropShim => "vtable_drop_shim",
        }
    }
}
