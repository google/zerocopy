//! Proptest strategies for generating [`TriHashMap`]s with random inputs.

use crate::{
    TriHashItem,
    support::{
        alloc::{Allocator, Global},
        hash_builder::DefaultHashBuilder,
    },
    tri_hash_map::TriHashMap,
};
use core::{fmt, hash::BuildHasher};
use proptest::{
    arbitrary::{Arbitrary, StrategyFor, any_with},
    collection::{SizeRange, VecStrategy, VecValueTree},
    strategy::{NewTree, Strategy, ValueTree},
    test_runner::TestRunner,
};

/// Strategy to create [`TriHashMap`]s with a length in a certain range.
///
/// Created by the [`prop_strategy()`] function.
#[must_use = "strategies do nothing unless used"]
#[derive(Clone)]
pub struct TriHashMapStrategy<T, S = DefaultHashBuilder, A = Global>
where
    T: Strategy,
{
    inner: VecStrategy<T>,
    hasher: S,
    allocator: A,
}

impl<T, S, A> fmt::Debug for TriHashMapStrategy<T, S, A>
where
    T: Strategy,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TriHashMapStrategy")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

/// Creates a strategy to generate [`TriHashMap`]s containing items drawn from
/// `element` and with a size within the given range.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{TriHashItem, TriHashMap, tri_hash_map, tri_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
///     name: String,
/// }
///
/// impl TriHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///     type K3<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///     fn key3(&self) -> Self::K3<'_> {
///         &self.name
///     }
///     tri_upcast!();
/// }
///
/// // Create a strategy using a tuple and mapping it to Person.
/// let strategy = tri_hash_map::prop_strategy(
///     (any::<u32>(), any::<String>(), any::<String>())
///         .prop_map(|(id, email, name)| Person { id, email, name }),
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
) -> TriHashMapStrategy<T, DefaultHashBuilder, Global> {
    TriHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher: DefaultHashBuilder::default(),
        allocator: crate::support::alloc::global_alloc(),
    }
}

/// Creates a strategy to generate [`TriHashMap`]s with a custom hasher.
///
/// # Examples
///
/// ```
/// use iddqd::{TriHashItem, TriHashMap, tri_hash_map, tri_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
/// use std::collections::hash_map::RandomState;
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
///     name: String,
/// }
///
/// impl TriHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///     type K3<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///     fn key3(&self) -> Self::K3<'_> {
///         &self.name
///     }
///     tri_upcast!();
/// }
///
/// // Create a strategy with a custom hasher.
/// let hasher = RandomState::new();
/// let strategy = tri_hash_map::prop_strategy_with_hasher(
///     (any::<u32>(), any::<String>(), any::<String>())
///         .prop_map(|(id, email, name)| Person { id, email, name }),
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
) -> TriHashMapStrategy<T, S, Global> {
    let size = size.into();
    TriHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher,
        allocator: crate::support::alloc::global_alloc(),
    }
}

/// Creates a strategy to generate [`TriHashMap`]s with a custom hasher and
/// allocator.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "allocator-api2")] {
/// use allocator_api2::alloc::Global;
/// use iddqd::{TriHashItem, TriHashMap, tri_hash_map, tri_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
/// use std::collections::hash_map::RandomState;
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
///     name: String,
/// }
///
/// impl TriHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///     type K3<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///     fn key3(&self) -> Self::K3<'_> {
///         &self.name
///     }
///     tri_upcast!();
/// }
///
/// // Create a strategy with custom hasher and allocator.
/// let hasher = RandomState::new();
/// let allocator = Global;
/// let strategy = tri_hash_map::prop_strategy_with_hasher_in(
///     (any::<u32>(), any::<String>(), any::<String>())
///         .prop_map(|(id, email, name)| Person { id, email, name }),
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
) -> TriHashMapStrategy<T, S, A> {
    let size = size.into();
    TriHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher,
        allocator,
    }
}

impl<'a, T, S, A> Strategy for TriHashMapStrategy<T, S, A>
where
    T: Strategy,
    T::Value: 'a + TriHashItem,
    <T::Value as TriHashItem>::K1<'a>: fmt::Debug,
    <T::Value as TriHashItem>::K2<'a>: fmt::Debug,
    <T::Value as TriHashItem>::K3<'a>: fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Tree = TriHashMapValueTree<T::Tree, S, A>;
    type Value = TriHashMap<T::Value, S, A>;

    fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
        let inner = self.inner.new_tree(runner)?;

        Ok(TriHashMapValueTree {
            inner,
            hasher: self.hasher.clone(),
            allocator: self.allocator.clone(),
        })
    }
}

/// `ValueTree` corresponding to [`TriHashMapStrategy`].
#[derive(Clone)]
pub struct TriHashMapValueTree<T, S = DefaultHashBuilder, A = Global>
where
    T: ValueTree,
{
    inner: VecValueTree<T>,
    hasher: S,
    allocator: A,
}

impl<T, S, A> fmt::Debug for TriHashMapValueTree<T, S, A>
where
    T: ValueTree + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TriHashMapValueTree")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<'a, T, S, A> ValueTree for TriHashMapValueTree<T, S, A>
where
    T: ValueTree,
    T::Value: 'a + TriHashItem,
    <T::Value as TriHashItem>::K1<'a>: fmt::Debug,
    <T::Value as TriHashItem>::K2<'a>: fmt::Debug,
    <T::Value as TriHashItem>::K3<'a>: fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Value = TriHashMap<T::Value, S, A>;

    fn current(&self) -> Self::Value {
        let items = self.inner.current();
        let mut map = TriHashMap::with_hasher_in(
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

impl<'a, T, S, A> Arbitrary for TriHashMap<T, S, A>
where
    T: 'a + TriHashItem + Arbitrary,
    <T as TriHashItem>::K1<'a>: fmt::Debug,
    <T as TriHashItem>::K2<'a>: fmt::Debug,
    <T as TriHashItem>::K3<'a>: fmt::Debug,
    S: Clone + BuildHasher + Default,
    A: Clone + Allocator + Default,
{
    type Parameters = (SizeRange, T::Parameters);
    type Strategy = TriHashMapStrategy<StrategyFor<T>, S, A>;

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
