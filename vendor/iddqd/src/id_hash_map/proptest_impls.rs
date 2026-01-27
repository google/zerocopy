//! Proptest strategies for generating [`IdHashMap`]s with random inputs.

use crate::{
    IdHashItem,
    id_hash_map::IdHashMap,
    support::{
        alloc::{Allocator, Global},
        hash_builder::DefaultHashBuilder,
    },
};
use core::{fmt, hash::BuildHasher};
use proptest::{
    arbitrary::{Arbitrary, StrategyFor, any_with},
    collection::{SizeRange, VecStrategy, VecValueTree},
    strategy::{NewTree, Strategy, ValueTree},
    test_runner::TestRunner,
};

/// Strategy to create [`IdHashMap`]s with a length in a certain range.
///
/// Created by the [`prop_strategy()`] function.
#[must_use = "strategies do nothing unless used"]
#[derive(Clone)]
pub struct IdHashMapStrategy<T, S = DefaultHashBuilder, A = Global>
where
    T: Strategy,
{
    inner: VecStrategy<T>,
    hasher: S,
    allocator: A,
}

impl<T, S, A> fmt::Debug for IdHashMapStrategy<T, S, A>
where
    T: Strategy,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IdHashMapStrategy")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

/// Creates a strategy to generate [`IdHashMap`]s containing items drawn from
/// `element` and with a size within the given range.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdHashItem, IdHashMap, id_hash_map, id_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     name: String,
/// }
///
/// impl IdHashItem for Person {
///     type Key<'a> = u32;
///
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// // Create a strategy using a tuple and mapping it to Person.
/// let strategy = id_hash_map::prop_strategy(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, name)| Person { id, name }),
///     0..=5,
/// );
///
/// // The strategy can be used in proptest contexts.
/// let mut runner = TestRunner::default();
/// let _tree = strategy.new_tree(&mut runner).unwrap();
/// # }
/// ```
#[cfg(feature = "default-hasher")]
pub fn prop_strategy<T: Strategy>(
    element: T,
    size: impl Into<SizeRange>,
) -> IdHashMapStrategy<T, DefaultHashBuilder, Global> {
    IdHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher: DefaultHashBuilder::default(),
        allocator: crate::support::alloc::global_alloc(),
    }
}

/// Creates a strategy to generate [`IdHashMap`]s with a custom hasher.
///
/// # Examples
///
/// ```
/// use iddqd::{IdHashItem, IdHashMap, id_hash_map, id_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
/// use std::collections::hash_map::RandomState;
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     name: String,
/// }
///
/// impl IdHashItem for Person {
///     type Key<'a> = u32;
///
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// // Create a strategy with a custom hasher.
/// let hasher = RandomState::new();
/// let strategy = id_hash_map::prop_strategy_with_hasher(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, name)| Person { id, name }),
///     0..=3,
///     hasher,
/// );
///
/// // The strategy can be used in proptest contexts.
/// let mut runner = TestRunner::default();
/// let _tree = strategy.new_tree(&mut runner).unwrap();
/// ```
pub fn prop_strategy_with_hasher<T: Strategy, S>(
    element: T,
    size: impl Into<SizeRange>,
    hasher: S,
) -> IdHashMapStrategy<T, S, Global> {
    let size = size.into();
    IdHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher,
        allocator: crate::support::alloc::global_alloc(),
    }
}

/// Creates a strategy to generate [`IdHashMap`]s with a custom hasher and
/// allocator.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "allocator-api2")] {
/// use allocator_api2::alloc::Global;
/// use iddqd::{IdHashItem, IdHashMap, id_hash_map, id_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
/// use std::collections::hash_map::RandomState;
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     name: String,
/// }
///
/// impl IdHashItem for Person {
///     type Key<'a> = u32;
///
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// // Create a strategy with custom hasher and allocator.
/// let hasher = RandomState::new();
/// let allocator = Global;
/// let strategy = id_hash_map::prop_strategy_with_hasher_in(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, name)| Person { id, name }),
///     1..=4,
///     hasher,
///     allocator,
/// );
///
/// // The strategy can be used in proptest contexts.
/// let mut runner = TestRunner::default();
/// let _tree = strategy.new_tree(&mut runner).unwrap();
/// # }
/// ```
pub fn prop_strategy_with_hasher_in<T: Strategy, S, A>(
    element: T,
    size: impl Into<SizeRange>,
    hasher: S,
    allocator: A,
) -> IdHashMapStrategy<T, S, A> {
    let size = size.into();
    IdHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher,
        allocator,
    }
}

impl<'a, T, S, A> Strategy for IdHashMapStrategy<T, S, A>
where
    T: Strategy,
    T::Value: 'a + IdHashItem,
    <T::Value as IdHashItem>::Key<'a>: fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Tree = IdHashMapValueTree<T::Tree, S, A>;
    type Value = IdHashMap<T::Value, S, A>;

    fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
        let inner = self.inner.new_tree(runner)?;

        Ok(IdHashMapValueTree {
            inner,
            hasher: self.hasher.clone(),
            allocator: self.allocator.clone(),
        })
    }
}

/// `ValueTree` corresponding to [`IdHashMapStrategy`].
#[derive(Clone)]
pub struct IdHashMapValueTree<T, S = DefaultHashBuilder, A = Global>
where
    T: ValueTree,
{
    inner: VecValueTree<T>,
    hasher: S,
    allocator: A,
}

impl<T, S, A> fmt::Debug for IdHashMapValueTree<T, S, A>
where
    T: ValueTree + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IdHashMapValueTree")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<'a, T, S, A> ValueTree for IdHashMapValueTree<T, S, A>
where
    T: ValueTree,
    T::Value: 'a + IdHashItem,
    <T::Value as IdHashItem>::Key<'a>: fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Value = IdHashMap<T::Value, S, A>;

    fn current(&self) -> Self::Value {
        let items = self.inner.current();
        let mut map = IdHashMap::with_capacity_and_hasher_in(
            items.len(),
            self.hasher.clone(),
            self.allocator.clone(),
        );

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

impl<'a, T, S, A> Arbitrary for IdHashMap<T, S, A>
where
    T: 'a + IdHashItem + Arbitrary,
    <T as IdHashItem>::Key<'a>: fmt::Debug,
    S: Clone + BuildHasher + Default,
    A: Clone + Allocator + Default,
{
    type Parameters = (SizeRange, T::Parameters);
    type Strategy = IdHashMapStrategy<StrategyFor<T>, S, A>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        let (size, element_args) = args;
        prop_strategy_with_hasher_in(
            any_with::<T>(element_args),
            size,
            S::default(),
            A::default(),
        )
    }
}
