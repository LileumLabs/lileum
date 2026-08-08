#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// A Vec<T> wrapper which only allows the length to be a power of
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
}
