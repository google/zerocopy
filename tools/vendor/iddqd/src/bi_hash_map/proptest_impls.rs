//! Proptest strategies for generating [`BiHashMap`]s with random inputs.

use crate::{
    BiHashItem,
    bi_hash_map::BiHashMap,
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

/// Strategy to create [`BiHashMap`]s with a length in a certain range.
///
/// Created by the [`prop_strategy()`] function.
#[must_use = "strategies do nothing unless used"]
#[derive(Clone)]
pub struct BiHashMapStrategy<T, S = DefaultHashBuilder, A = Global>
where
    T: Strategy,
{
    inner: VecStrategy<T>,
    hasher: S,
    allocator: A,
}

impl<T, S, A> fmt::Debug for BiHashMapStrategy<T, S, A>
where
    T: Strategy,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BiHashMapStrategy")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

/// Creates a strategy to generate [`BiHashMap`]s containing items drawn from
/// `element` and with a size within the given range.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, BiHashMap, bi_hash_map, bi_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
/// }
///
/// impl BiHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///     bi_upcast!();
/// }
///
/// // Create a strategy using a tuple and mapping it to Person.
/// let strategy = bi_hash_map::prop_strategy(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, email)| Person { id, email }),
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
) -> BiHashMapStrategy<T, DefaultHashBuilder, Global> {
    BiHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher: DefaultHashBuilder::default(),
        allocator: crate::support::alloc::global_alloc(),
    }
}

/// Creates a strategy to generate [`BiHashMap`]s with a custom hasher.
///
/// # Examples
///
/// ```
/// use iddqd::{BiHashItem, BiHashMap, bi_hash_map, bi_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
/// use std::collections::hash_map::RandomState;
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
/// }
///
/// impl BiHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///     bi_upcast!();
/// }
///
/// // Create a strategy with a custom hasher.
/// let hasher = RandomState::new();
/// let strategy = bi_hash_map::prop_strategy_with_hasher(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, email)| Person { id, email }),
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
) -> BiHashMapStrategy<T, S, Global> {
    let size = size.into();
    BiHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher,
        allocator: crate::support::alloc::global_alloc(),
    }
}

/// Creates a strategy to generate [`BiHashMap`]s with a custom hasher and
/// allocator.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "allocator-api2")] {
/// use allocator_api2::alloc::Global;
/// use iddqd::{BiHashItem, BiHashMap, bi_hash_map, bi_upcast};
/// use proptest::{
///     arbitrary::any, strategy::Strategy, test_runner::TestRunner,
/// };
/// use std::collections::hash_map::RandomState;
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
/// }
///
/// impl BiHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///     bi_upcast!();
/// }
///
/// // Create a strategy with custom hasher and allocator.
/// let hasher = RandomState::new();
/// let allocator = Global;
/// let strategy = bi_hash_map::prop_strategy_with_hasher_in(
///     (any::<u32>(), any::<String>())
///         .prop_map(|(id, email)| Person { id, email }),
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
) -> BiHashMapStrategy<T, S, A> {
    let size = size.into();
    BiHashMapStrategy {
        inner: proptest::collection::vec(element, size),
        hasher,
        allocator,
    }
}

impl<'a, T, S, A> Strategy for BiHashMapStrategy<T, S, A>
where
    T: Strategy,
    T::Value: 'a + BiHashItem,
    <T::Value as BiHashItem>::K1<'a>: fmt::Debug,
    <T::Value as BiHashItem>::K2<'a>: fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Tree = BiHashMapValueTree<T::Tree, S, A>;
    type Value = BiHashMap<T::Value, S, A>;

    fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
        let inner = self.inner.new_tree(runner)?;

        Ok(BiHashMapValueTree {
            inner,
            hasher: self.hasher.clone(),
            allocator: self.allocator.clone(),
        })
    }
}

/// `ValueTree` corresponding to [`BiHashMapStrategy`].
#[derive(Clone)]
pub struct BiHashMapValueTree<T, S = DefaultHashBuilder, A = Global>
where
    T: ValueTree,
{
    inner: VecValueTree<T>,
    hasher: S,
    allocator: A,
}

impl<T, S, A> fmt::Debug for BiHashMapValueTree<T, S, A>
where
    T: ValueTree + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BiHashMapValueTree")
            .field("inner", &self.inner)
            .finish_non_exhaustive()
    }
}

impl<'a, T, S, A> ValueTree for BiHashMapValueTree<T, S, A>
where
    T: ValueTree,
    T::Value: 'a + BiHashItem,
    <T::Value as BiHashItem>::K1<'a>: fmt::Debug,
    <T::Value as BiHashItem>::K2<'a>: fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Value = BiHashMap<T::Value, S, A>;

    fn current(&self) -> Self::Value {
        let items = self.inner.current();
        let mut map = BiHashMap::with_hasher_in(
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

impl<'a, T, S, A> Arbitrary for BiHashMap<T, S, A>
where
    T: 'a + BiHashItem + Arbitrary,
    <T as BiHashItem>::K1<'a>: fmt::Debug,
    <T as BiHashItem>::K2<'a>: fmt::Debug,
    S: Clone + BuildHasher + Default,
    A: Clone + Allocator + Default,
{
    type Parameters = (SizeRange, T::Parameters);
    type Strategy = BiHashMapStrategy<StrategyFor<T>, S, A>;

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
