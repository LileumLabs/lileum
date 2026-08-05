use ark_ff::Field;

/// A point with `n` variables
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiPoint<F: Field>(Vec<F>);

impl<F: Field> From<Vec<F>> for MultiPoint<F> {
    fn from(value: Vec<F>) -> Self {
        Self(value)
    }
}

impl<F: Field> From<&[F]> for MultiPoint<F> {
    fn from(value: &[F]) -> Self {
        Self(value.to_vec())
    }
}

impl<F: Field> AsRef<[F]> for MultiPoint<F> {
    fn as_ref(&self) -> &[F] {
        &self.0
    }
}

impl<F: Field> MultiPoint<F> {
    pub fn new(vars: Vec<F>) -> Self {
        MultiPoint(vars)
    }
    pub fn new_from_index(mut index: usize, vars: usize) -> Self {
        let vars = (0..vars)
            .map(|_| {
                let var = if index & 0b1 == 1 { F::ONE } else { F::ZERO };
                index >>= 1;
                var
            })
            .collect();
        MultiPoint::new(vars)
    }
    pub fn vars(&self) -> usize {
        self.0.len()
    }
    pub fn inner(self) -> Vec<F> {
        self.0
    }
    pub fn inner_ref(&self) -> &[F] {
        &self.0
    }
    /// eval self as eq poly with point
    pub fn eval_as_eq(&self, point: &Self) -> F {
        assert_eq!(self.0.len(), point.0.len());
        self.0
            .iter()
            .zip(point.0.iter())
            .fold(F::one(), |acc, (a, b)| {
                let var = *a * b + (F::one() - a) * (F::one() - b);
                acc * var
            })
    }
}
