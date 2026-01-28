//! A two dimensional collection whose purpose it to reduce heap allocations.
//!
//! This crate is intended to be used when:
//! - you want a potentially large:
//!   - `Vec<String>`
//!   - `Vec<Vec<T>>`
//!   - `Vec<C>` where `C` is heap allocated, dynamically sized and can implement `Collection` trait
//! - you actually only need to use borrowed items (`&[T]` or `&str`)
//!
//! Instead of having n + 1 allocations, you'll only have 2.
//!
//! # Example
//!
//! ```rust
//! use nested::Nested;
//!
//! let mut v = Nested::<String>::new();
//!
//! // you can either populate it one by one
//! v.push("a");
//! v.push("bb".to_string());
//! v.push("hhh");
//! v.extend(vec!["iiiiii".to_string(), "jjjj".to_string()]);
//! assert_eq!(v.len(), 5);
//! assert_eq!(&v[0], "a");
//! assert_eq!(&v[1], "bb");
//!
//! // or you can directly collect it
//! let mut v = ["a", "b", "c", "d", "e", "f", "g"].iter().collect::<Nested<String>>();
//! assert_eq!(v.len(), 7);
//!
//! // it also provides basic operations
//! let u = v.split_off(2);
//! assert_eq!(u.get(0), Some("c"));
//!
//! v.truncate(1);
//! assert_eq!(v.pop(), Some("a".to_string()));
//! assert_eq!(v.pop(), None);
//! ```
use std::iter::{repeat, FromIterator};
use std::ops::{Index, Range};

/// A `Nested` item when `T: Collection`
pub type Item<T> = <T as Index<Range<usize>>>::Output;
/// A `Nested<String>`
pub type ZString = Nested<String>;
/// A `Nested<Vec<T>>`
pub type ZVec<T> = Nested<Vec<T>>;

/// A `Collection` trait to expose basic required fn for `Nested` to work properly
pub trait Collection: Index<Range<usize>> {
    fn new() -> Self;
    fn with_capacity(cap: usize) -> Self;
    fn len(&self) -> usize;
    fn truncate(&mut self, len: usize);
    fn extend_from_slice(&mut self, s: &<Self as Index<Range<usize>>>::Output);
    fn split_off(&mut self, at: usize) -> Self;
}

impl<T: Clone> Collection for Vec<T> {
    fn len(&self) -> usize {
        self.len()
    }
    fn new() -> Self {
        Vec::new()
    }
    fn with_capacity(cap: usize) -> Self {
        Vec::with_capacity(cap)
    }
    fn truncate(&mut self, len: usize) {
        self.truncate(len);
    }
    fn extend_from_slice(&mut self, s: &<Self as Index<Range<usize>>>::Output) {
        Vec::extend_from_slice(self, s)
    }
    fn split_off(&mut self, at: usize) -> Self {
        self.split_off(at)
    }
}

impl Collection for String {
    fn len(&self) -> usize {
        self.len()
    }
    fn new() -> Self {
        String::new()
    }
    fn with_capacity(cap: usize) -> Self {
        String::with_capacity(cap)
    }
    fn truncate(&mut self, len: usize) {
        self.truncate(len);
    }
    fn extend_from_slice(&mut self, s: &<Self as Index<Range<usize>>>::Output) {
        self.push_str(s)
    }
    fn split_off(&mut self, at: usize) -> Self {
        self.split_off(at)
    }
}

/// A two dimensional collection with minimal allocation
///
/// `T` is the owning underlying container.
///
/// For instance, it behaves similarly to `Vec<Vec<T>>` or `Vec<String>` but
/// only has 2 internal buffers.
///
/// It can be used:
/// - on your own collection as long as it implements the `Collection` trait.
/// - like a sparse vector
/// - when you need to collect (move ownership) many `String`s or `Vec<T>`s
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct Nested<T> {
    indices: Vec<usize>,
    data: T,
}

impl<T: Collection> Nested<T> {
    /// Create a new `Nested`.
    pub fn new() -> Self {
        Nested {
            indices: vec![0],
            data: T::new(),
        }
    }

    /// Creates a new `Nested` with given capacity.
    ///
    /// len: the expected item count
    /// size: the expected total size taken by all items
    pub fn with_capacity(len: usize, size: usize) -> Self {
        let mut indices = Vec::with_capacity(len + 1);
        indices.push(0);
        Nested {
            indices: indices,
            data: T::with_capacity(size),
        }
    }

    /// Pushes a new item
    pub fn push<I: AsRef<Item<T>>>(&mut self, el: I) {
        self.data.extend_from_slice(el.as_ref());
        let len = self.data.len();
        self.indices.push(len);
    }

    /// Removes the last element from a `Nested` and returns it, or None if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.indices.len() > 1 {
            let l = self.indices[self.indices.len() - 2];
            let data = self.data.split_off(l);
            self.indices.pop();
            Some(data)
        } else {
            None
        }
    }

    /// Extend with `count` empty elements
    pub fn extend_empty(&mut self, count: usize) {
        let len = self.data.len();
        self.indices.extend(repeat(len).take(count));
    }

    /// Returns the number of elements in the `Nested`.
    #[inline]
    pub fn len(&self) -> usize {
        self.indices.len() - 1
    }

    /// Get the total length taken by the data
    #[inline]
    pub fn data_len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if self has a length of zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Shortens the `Nested`, keeping the first len elements and dropping the rest.
    ///
    /// If len is greater than the vector's current length, this has no effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the vector.
    pub fn truncate(&mut self, len: usize) {
        if len + 1 >= self.indices.len() {
            return;
        }

        let size = self.indices[len];
        self.indices.truncate(len + 1);
        self.data.truncate(size);
    }

    /// Truncates this `Nested`, removing all contents.
    ///
    /// While this means the `Nested` will have a length of zero, it does not touch its capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.indices.truncate(1);
        self.data.truncate(0);
    }

    /// Returns a shared reference to the output at this location, if in bounds.
    pub fn get(&self, index: usize) -> Option<&Item<T>> {
        if index >= self.len() {
            None
        } else {
            Some(&self[index])
        }
    }

    /// Converts this `Nested` into its constituent parts.
    pub fn into_parts(self) -> (Vec<usize>, T) {
        (self.indices, self.data)
    }

    /// Returns a reference to the underlying indices.
    ///
    /// Each index represents the start of each logical vector beyond the first one.
    pub fn indices(&self) -> &[usize] {
        &self.indices
    }

    /// Returns a reference to the underlying data.
    ///
    /// The data is stored contiguously.
    pub fn data(&self) -> &T {
        &self.data
    }

    /// Returns an iterator over `Nested` elements.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            windows: self.indices.windows(2),
            data: &self.data,
        }
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated Self. self contains elements [0, at), and the returned Self
    /// contains elements [at, len).
    ///
    /// Note that the capacity of self does not change.
    pub fn split_off(&mut self, at: usize) -> Nested<T> {
        if at == self.len() {
            return Nested::new();
        }
        assert!(at < self.len());
        let mut new_indices = self.indices.split_off(at + 1);
        let offset = self.indices[at];
        let new_data = self.data.split_off(offset);
        for i in &mut new_indices {
            *i -= offset;
        }
        new_indices.insert(0, 0);
        Nested {
            indices: new_indices,
            data: new_data,
        }
    }
}

impl<T: Collection> Index<usize> for Nested<T> {
    type Output = Item<T>;
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index + 1 <= self.indices.len());
        let lo = self.indices[index];
        let hi = self.indices[index + 1];
        &self.data.index(lo..hi)
    }
}

impl<T: Collection, A: AsRef<Item<T>>> Extend<A> for Nested<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator,
        I::Item: AsRef<Item<T>>,
    {
        for i in iter.into_iter() {
            self.push(i);
        }
    }
}

/// An iterator over `Nested` elements
#[derive(Debug, Clone)]
pub struct Iter<'a, T: 'a> {
    windows: ::std::slice::Windows<'a, usize>,
    data: &'a T,
}

impl<'a, T: Collection> Iterator for Iter<'a, T> {
    type Item = &'a Item<T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.windows.next().map(|w| self.data.index(w[0]..w[1]))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.windows.size_hint()
    }
}

impl<'a, T: Collection> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.windows.len()
    }
}

impl<'a, T: Collection> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<<Self as Iterator>::Item> {
        self.windows
            .next_back()
            .map(|w| self.data.index(w[0]..w[1]))
    }
}

impl<T: Collection, A: AsRef<Item<T>>> FromIterator<A> for Nested<T> {
    fn from_iter<I: IntoIterator<Item = A>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut v = match iter.size_hint() {
            (0, None) => Nested::new(),
            (_, Some(l)) | (l, None) => Nested::with_capacity(l, l * 4),
        };
        v.extend(iter);
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string() {
        let mut v = Nested::<String>::new();
        v.push("aaa");
        v.push("bbb".to_string());
        assert_eq!(v.len(), 2);
        assert_eq!(&v[0], "aaa");
        assert_eq!(&v[1], "bbb");
        v.truncate(1);
        assert_eq!(v.len(), 1);
        assert_eq!(&v[0], "aaa");
        assert_eq!(v.get(1), None);
        v.extend_empty(3);
        assert_eq!(v.len(), 4);
        assert_eq!(&v[2], "");
    }

    #[test]
    fn test_vec() {
        let mut v = Nested::<Vec<_>>::new();
        v.push(&[1, 2, 3]);
        v.push(vec![1, 2, 4]);
        assert_eq!(v.len(), 2);
        assert_eq!(&v[0], &[1, 2, 3]);
        assert_eq!(&v[1], &[1, 2, 4]);
        v.truncate(1);
        assert_eq!(v.len(), 1);
        assert_eq!(&v[0], &[1, 2, 3]);
        assert_eq!(v.get(1), None);
        v.extend_empty(3);
        assert_eq!(v.len(), 4);
        assert_eq!(&v[2], &[]);
    }

    #[test]
    fn test_collect() {
        let sce = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
        ];
        let v = sce.iter().collect::<Nested<String>>();
        assert_eq!(v.len(), 4);
        assert_eq!(&v[0], "a");
        assert_eq!(&v[1], "b");
        assert_eq!(&v[2], "c");
        assert_eq!(&v[3], "d");

        let sce = vec!["a", "b", "c", "d"];
        let v2 = sce.iter().collect::<Nested<String>>();
        assert_eq!(v, v2);
    }

    #[test]
    fn test_iter() {
        let sce = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
        ];
        let v = sce.iter().collect::<Nested<String>>();
        let new_sce = v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert_eq!(sce, new_sce);
    }

    #[test]
    fn test_split_off() {
        let mut v = ["a", "b", "c", "d"].iter().collect::<Nested<String>>();
        assert_eq!(v.len(), 4);
        let u = v.split_off(2);
        assert_eq!(v.len(), 2);
        assert_eq!(u.len(), 2);
        assert!(v.iter().zip(["a", "b"].iter()).all(|(r, l)| l.eq(&r)));
        assert!(u.iter().zip(["c", "d"].iter()).all(|(r, l)| l.eq(&r)));
    }

    #[test]
    fn test_pop() {
        let mut v = ["a", "b", "c", "d"].iter().collect::<Nested<String>>();
        assert_eq!(v.len(), 4);
        assert_eq!(v.pop(), Some("d".to_string()));
        assert_eq!(v.len(), 3);
        assert_eq!(v.pop(), Some("c".to_string()));
        assert_eq!(v.len(), 2);
        assert_eq!(v.pop(), Some("b".to_string()));
        assert_eq!(v.len(), 1);
        assert_eq!(v.pop(), Some("a".to_string()));
        assert_eq!(v.len(), 0);
        assert_eq!(v.pop(), None);
        assert_eq!(v.len(), 0);
    }
}
