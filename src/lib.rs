use std::{
    borrow::Borrow,
    collections::{hash_map, HashMap, TryReserveError},
    hash::{BuildHasher, Hash, RandomState},
    iter::{once, Chain, FlatMap, Flatten, Once},
};

#[derive(Clone, Debug, Default)]
pub struct HashMultiSet<T, S = RandomState> {
    data: HashMap<T, Vec<T>, S>,
    len: usize,
}

impl<T> HashMultiSet<T, RandomState> {
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
            len: 0,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: HashMap::with_capacity(capacity),
            len: 0,
        }
    }
}

impl<T, S> HashMultiSet<T, S> {
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    pub fn iter(&self) -> Iter<'_, T> {
        self.data.keys().chain(self.data.values().flatten())
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    // TODO: Implement `drain` method

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.data.retain(|k, _| f(k));
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.len = 0;
    }

    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            data: HashMap::with_hasher(hash_builder),
            len: 0,
        }
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            data: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            len: 0,
        }
    }

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
