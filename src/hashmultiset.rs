use std::{
    borrow::Borrow,
    collections::{hash_map, HashMap, TryReserveError},
    hash::{BuildHasher, Hash, RandomState},
    iter::{once, Chain, FlatMap, Flatten, Once},
};

/// A hash multi set implemented using a `HashMap`.
///
/// A HashMultiSet requires that the elements implement the [`Eq`] and [`Hash`] traits.
/// Two values which are equal by [`Eq`] treated as exactly equal by the HashMultiSet.
/// So HashMultiSet treats the following assumption as true:
/// ```text
/// a == b -> f(a) == f(b)
/// ```
///
/// The HashMultiSet is implemented using a `HashMap` where the key is the element and the value is a `Vec` of the duplicate element.
/// So, the HashMultiSet can store multiple copies of the same element.
/// Inserting the duplicate element will cause alocate a new `Vec` and store the element in it.
/// So, it is recommended to use [`HashBag`] from the `hashbag` crate if you want to store elements which implement the [`Copy`] trait.
///
/// # Examples
///
/// ```
/// use ktvvtmultiset::HashMultiSet;
/// let mut books = HashMultiSet::new();
///
/// // Add Some Books
/// books.insert("A Song of Ice and Fire");
/// books.insert("A Song of Ice and Fire");
/// books.insert("A Song of Ice and Fire");
/// books.insert("The Name of the Wind");
/// books.insert("The Name of the Wind");
/// books.insert("Prince of Thorns");
/// books.insert("The Lies of Locke Lamora");
///
/// // Check for the specific one
/// if !books.contains("The Blade Itself") {
///    println!("We have {} books, but The Blade Itself ain't one.",
///        books.len());
/// }
///
/// // Remove a book
/// books.remove("The Name of the Wind");
/// // The book still exists
/// assert!(books.contains("The Name of the Wind"));
///
/// // Remove all books with the same name
/// books.remove_all("The Name of the Wind");
/// assert!(!books.contains("The Name of the Wind"));
///
/// // Iterate over everything
/// for book in &books {
///    println!("{book}");
/// }
/// ```
#[derive(Clone, Debug, Default)]
pub struct HashMultiSet<T, S = RandomState> {
    data: HashMap<T, Vec<T>, S>,
    len: usize,
}

impl<T> HashMultiSet<T, RandomState> {
    /// Creates a new empty `HashMultiSet`.
    ///
    /// The HashMultiSet is initially created with a capacity of 0, so it will not allocate until it is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let multiset: HashMultiSet<i32> = HashMultiSet::new();
    /// ```
    #[inline]
    pub fn new() -> HashMultiSet<T, RandomState> {
        Self {
            data: HashMap::new(),
            len: 0,
        }
    }

    /// Creates a new empty `HashMultiSet` with the specified capacity.
    ///
    /// The HashMultiSet will be able to hold at least `capacity` unique elements without reallocating.
    /// Noted that duplicate elements will be stored in a `Vec` so inserting the duplicate element will cause alocate a new `Vec`.
    /// If `capacity` is 0, the HashMultiSet will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let multiset: HashMultiSet<i32> = HashMultiSet::with_capacity(10);
    /// assert!(multiset.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: HashMap::with_capacity(capacity),
            len: 0,
        }
    }
}

impl<T, S> HashMultiSet<T, S> {
    /// Returns the number of unique elements the set can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let multiset: HashMultiSet<i32> = HashMultiSet::with_capacity(100);
    /// assert!(multiset.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// An iterator visiting all elements in arbitrary order. The iterator element type is &'a T.
    ///
    /// # Examples
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let mut multiset = HashMultiSet::new();
    /// multiset.insert(1);
    /// multiset.insert(2);
    /// multiset.insert(2);
    /// multiset.insert(3);
    ///
    /// // Will print in an arbitrary order.
    /// for x in multiset.iter() {
    ///    println!("{x}");
    /// }
    /// ```
    ///
    /// # Performance
    /// In the current implementation, over set takes O(capacity + len - uniaue_len) time instead of O(len)
    /// because it internally visits empty buckets too.
    pub fn iter(&self) -> Iter<'_, T> {
        self.data.keys().chain(self.data.values().flatten())
    }

    /// Returns the number of elements in the set, including duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let mut multiset = HashMultiSet::new();
    /// multiset.insert(1);
    /// multiset.insert(2);
    /// assert_eq!(multiset.len(), 2);
    /// multiset.insert(2);
    /// assert_eq!(multiset.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the number of unique elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let mut multiset = HashMultiSet::new();
    /// multiset.insert(1);
    /// multiset.insert(2);
    /// assert_eq!(multiset.unique_len(), 2);
    /// multiset.insert(2);
    /// assert_eq!(multiset.unique_len(), 2);
    /// ```
    pub fn unique_len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    /// let mut multiset = HashMultiSet::new();
    /// assert!(multiset.is_empty());
    /// multiset.insert(1);
    /// assert!(!multiset.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn drain(&mut self) -> hash_map::Drain<T, Vec<T>> {
        unimplemented!()
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements e for which f(&e) returns false.
    /// The elements are visited in unsorted (and unspecified) order.
    /// Logical errors occur if the following are not met:
    ///
    /// ```text
    /// e1 == e2 -> f(&e1) == f(&e2)
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    ///
    /// let mut multiset = HashMultiSet::from([1, 2, 3, 3, 4, 4, 5, 6]);
    /// multiset.retain(|&x| x % 2 == 0);
    /// assert_eq!(multiset, HashMultiSet::from([2, 4, 4, 6]));
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, this operation takes O(capacity) time.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut deleted = 0;
        self.data.retain(|k, v| {
            let t = f(k);
            if !t {
                deleted += v.len() + 1;
            }
            t
        });
        self.len -= deleted;
    }

    /// Clears the set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use ktvvtmultiset::HashMultiSet;
    ///
    /// let mut multiset = HashMultiSet::new();
    /// multiset.insert(1);
    /// multiset.clear();
    /// assert!(multiset.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.data.clear();
        self.len = 0;
    }

    /// Creates a new empty set which will use the given hasher to hash keys.
    ///
    /// The set is also created with the default initial capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use ktvvtmultiset::HashMultiSet;
    ///
    /// let s = RandomState::new();
    /// let mut set = HashMultiSet::with_hasher(s);
    /// set.insert(2);
    /// ```
    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            data: HashMap::with_hasher(hash_builder),
            len: 0,
        }
    }

    /// Creates a new empty set with the specified capacity, using the given hasher to hash keys.
    ///
    /// See [`.with_hasher()`](HashMultiSet::with_hasher) and [`.with_capacity()`](HashMultiSet::with_capacity) for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use ktvvtmultiset::HashMultiSet;
    ///
    /// let s = RandomState::new();
    /// let mut set = HashMultiSet::with_capacity_and_hasher(10, s);
    /// set.insert(1);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            data: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            len: 0,
        }
    }

    /// Returns a reference to the set's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use ktvvtmultiset::HashMultiSet;
    ///
    /// let s = RandomState::new();
    /// let set: HashMultiSet<i32> = HashMultiSet::with_hasher(s);
    /// let hasher: &RandomState = set.hasher();
    /// ```
    pub fn hasher(&self) -> &S {
        self.data.hasher()
    }
}

impl<T, S> HashMultiSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    pub fn reserve(&mut self, additional: usize) {
        self.data.reserve(additional);
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.data.try_reserve(additional)
    }

    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.data.shrink_to(min_capacity);
    }

    // TODO: Implement `diffrence` method
    // TODO: Implement `symmetric_difference` method
    // TODO: Implement `intersection` method

    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.data.contains_key(value)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        if self.len() <= other.len() {
            self.data.keys().all(|v| !other.contains(v))
        } else {
            other.data.keys().all(|v| !self.contains(v))
        }
    }

    pub fn insert(&mut self, value: T) {
        self.len += 1;
        #[allow(clippy::map_entry)]
        if self.data.contains_key(&value) {
            self.data.get_mut(&value).unwrap().push(value);
        } else {
            self.data.insert(value, vec![]);
        }
    }

    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(v) = self.data.get_mut(value) {
            if v.is_empty() {
                self.data.remove(value);
            } else {
                self.len -= 1;
            }
            true
        } else {
            false
        }
    }

    pub fn remove_all<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(v) = self.data.get_mut(value) {
            self.len -= v.len();
            self.data.remove(value);
            true
        } else {
            false
        }
    }

    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(v) = self.data.get_mut(value) {
            if let Some(t) = v.pop() {
                self.len -= 1;
                if v.is_empty() {
                    self.data.remove(value);
                }
                Some(t)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<T, S> Extend<T> for HashMultiSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter {
            self.insert(elem);
        }
    }
}

impl<T, const N: usize> From<[T; N]> for HashMultiSet<T>
where
    T: Eq + Hash,
{
    fn from(arr: [T; N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<T, S> FromIterator<T> for HashMultiSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::with_hasher(Default::default());
        set.extend(iter);
        set
    }
}

impl<'a, T, S> IntoIterator for &'a HashMultiSet<T, S> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> IntoIterator for HashMultiSet<T> {
    type Item = T;
    type IntoIter = FlatMap<
        hash_map::IntoIter<T, Vec<T>>,
        Chain<Once<T>, std::vec::IntoIter<T>>,
        fn((T, Vec<T>)) -> Chain<Once<T>, std::vec::IntoIter<T>>,
    >;

    fn into_iter(self) -> Self::IntoIter {
        fn f<T>((k, v): (T, Vec<T>)) -> Chain<Once<T>, std::vec::IntoIter<T>> {
            once(k).chain(v)
        }
        self.data.into_iter().flat_map(f)
    }
}

impl<T, S> PartialEq for HashMultiSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        self.data
            .iter()
            .all(|(k, v)| other.data.get(k).map_or(false, |ov| ov.len() == v.len()))
    }
}

impl<T, S> Eq for HashMultiSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

pub type Iter<'a, T> =
    Chain<hash_map::Keys<'a, T, Vec<T>>, Flatten<hash_map::Values<'a, T, Vec<T>>>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {}
}
