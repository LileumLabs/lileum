use std::iter::repeat;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// A `Vec<T>` wrapper which only allows the length to be a power of
/// two.
pub struct Pow2Vec<T>(Vec<T>);

impl<T> Pow2Vec<T> {
    /// Panics if length is not a power of two.
    pub fn new(items: Vec<T>) -> Self {
        assert!(items.len().is_power_of_two());
        Self(items)
    }

    pub fn inner(&self) -> &[T] {
        &self.0
    }

    pub fn into_inner(self) -> Vec<T> {
        self.0
    }

    pub fn extend(&mut self, value: T)
    where
        T: Clone,
    {
        let len = self.0.len();
        self.0.resize(len * 2, value);
    }

    pub fn split(&self) -> (Self, Self)
    where
        T: Clone,
    {
        let vec = &self.0;
        let len = vec.len();
        let (left, right) = vec.split_at(len / 2);
        (Self(left.to_vec()), Self(right.to_vec()))
    }

    pub fn from_padded_slice(slice: &[T], pad_with: T) -> Self
    where
        T: Clone,
    {
        let len = slice.len().next_power_of_two();
        let padding = repeat(pad_with);
        Self(slice.iter().cloned().chain(padding).take(len).collect())
    }
}

impl<'a, T> IntoIterator for &'a Pow2Vec<T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.as_slice().iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Pow2Vec<T> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T> IntoIterator for Pow2Vec<T> {
    type Item = T;

    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
