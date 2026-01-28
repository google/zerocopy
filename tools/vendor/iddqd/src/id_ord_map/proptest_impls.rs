//! Proptest strategies for generating [`IdOrdMap`]s with random inputs.

use crate::{IdOrdItem, id_ord_map::IdOrdMap};
use core::fmt;
use proptest::{
    arbitrary::{Arbitrary, StrategyFor, any_with},
    collection::{SizeRange, VecStrategy, VecValueTree},
    strategy::{NewTree, Strategy, ValueTree},
    test_runner::TestRunner,
};

/// Strategy to create [`IdOrdMap`]s with a length in a certain range.
///
/// Created by the [`prop_strategy()`] function.
#[must_use = "strategies do nothing unless used"]
#[derive(Clone)]
pub struct IdOrdMapStrategy<T>
where
    T: Strategy,
{
    inner: VecStrategy<T>,
}

impl<T> fmt::Debug for IdOrdMapStrategy<T>
where
    T: Strategy,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IdOrdMapStrategy")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

/// Creates a strategy to generate [`IdOrdMap`]s containing items drawn from
/// `element` and with a size within the given range.
///
/// # Examples
///
/// ```
/// use iddqd::{IdOrdItem, IdOrdMap, id_ord_map, id_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
///
/// #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// struct Person {
///     id: u32,
///     name: String,
/// }
///
/// impl IdOrdItem for Person {
///     type Key<'a> = u32;
///
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// // Create a strategy using a tuple and mapping it to Person.
/// let strategy = id_ord_map::prop_strategy(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, name)| Person { id, name }),
///     0..=5,
/// );
///
/// // The strategy can be used in proptest contexts.
/// let mut runner = TestRunner::default();
/// let _tree = strategy.new_tree(&mut runner).unwrap();
/// ```
pub fn prop_strategy<T: Strategy>(
    element: T,
    size: impl Into<SizeRange>,
) -> IdOrdMapStrategy<T> {
    IdOrdMapStrategy { inner: proptest::collection::vec(element, size) }
}

impl<'a, T> Strategy for IdOrdMapStrategy<T>
where
    T: Strategy,
    T::Value: 'a + IdOrdItem,
    <T::Value as IdOrdItem>::Key<'a>: fmt::Debug,
{
    type Tree = IdOrdMapValueTree<T::Tree>;
    type Value = IdOrdMap<T::Value>;

    fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
        let inner = self.inner.new_tree(runner)?;

        Ok(IdOrdMapValueTree { inner })
    }
}

/// `ValueTree` corresponding to [`IdOrdMapStrategy`].
#[derive(Clone)]
pub struct IdOrdMapValueTree<T>
where
    T: ValueTree,
{
    inner: VecValueTree<T>,
}

impl<T> fmt::Debug for IdOrdMapValueTree<T>
where
    T: ValueTree + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IdOrdMapValueTree")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<'a, T> ValueTree for IdOrdMapValueTree<T>
where
    T: ValueTree,
    T::Value: 'a + IdOrdItem,
    <T::Value as IdOrdItem>::Key<'a>: fmt::Debug,
{
    type Value = IdOrdMap<T::Value>;

    fn current(&self) -> Self::Value {
        let items = self.inner.current();
        let mut map = IdOrdMap::new();

        for item in items {
            // Use insert_overwrite to handle duplicate keys.
            map.insert_overwrite(item);
        }

        map
    }

    fn simplify(&mut self) -> bool {
        self.inner.simplify()
    }

    fn complicate(&mut self) -> bool {
        self.inner.complicate()
    }
}

impl<'a, T> Arbitrary for IdOrdMap<T>
where
    T: 'a + IdOrdItem + Arbitrary,
    <T as IdOrdItem>::Key<'a>: fmt::Debug,
{
    type Parameters = (SizeRange, T::Parameters);
    type Strategy = IdOrdMapStrategy<StrategyFor<T>>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let (size, element_args) = args;
        prop_strategy(any_with::<T>(element_args), size)
    }
}
