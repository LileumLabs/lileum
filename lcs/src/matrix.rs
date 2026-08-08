use core::slice;
use std::ops::{Index, Mul};

use ark_ff::Field;

/// Sparse matrix.
#[derive(Default, Clone, Debug)]
pub struct Matrix {
    ///assumes each non zero value to be one, should be enough to represent plonk
    /// considering that most rows will likely have a single 1 the vector represation may be suboptimal
    rows: Vec<Vec<usize>>,
}

impl Matrix {
    /// number of rows
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.len() == 0
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Matrix {
            rows: Vec::with_capacity(capacity),
        }
    }

    pub fn push_row_single_value(&mut self, idx: usize) {
        self.rows.push(vec![idx])
    }

    pub(crate) fn push_row_empty(&mut self) {
        self.rows.push(vec![])
    }

    /// convert to sparse indexed evals as expected by spark
    pub fn to_evals(&self) -> Vec<(usize, usize)> {
        let mut evals = Vec::with_capacity(self.rows.len());
        for (i, cols) in self.rows.iter().enumerate() {
            for col in cols {
                evals.push((i, *col));
            }
        }
        evals
    }

    /// Returns a reference to the row in the given position or `None`
    /// if out of bounds.
    pub fn get_row(&self, index: usize) -> Option<&[usize]> {
        self.rows.get(index).map(Vec::as_slice)
    }

    /// Returns iterator over all non-zero cells, panics if the matrix is empty.
    pub fn iter(&self) -> CellIter<'_> {
        let mut rows = self.rows.iter();
        let current_row = rows.next().expect("matrix is empty").iter();
        CellIter {
            rows,
            current_row,
            current_row_idx: 0,
        }
    }
}

impl Index<usize> for Matrix {
    type Output = [usize];

    fn index(&self, index: usize) -> &Self::Output {
        &self.rows[index]
    }
}

/// Itertator over the cells of a matrix.
pub struct CellIter<'a> {
    rows: slice::Iter<'a, Vec<usize>>,
    current_row: slice::Iter<'a, usize>,
    current_row_idx: usize,
}

impl Iterator for CellIter<'_> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.current_row_idx;
        match self.current_row.next() {
            Some(c) => Some((idx, *c)),
            None => {
                let new_row = loop {
                    let row = self.rows.next()?;
                    self.current_row_idx += 1;
                    if !row.is_empty() {
                        break row;
                    }
                };
                let mut new_row = new_row.iter();
                let next = new_row.next();
                self.current_row = new_row;
                next.copied().map(|j| (self.current_row_idx, j))
            }
        }
    }
}

impl<F: Field> Mul<&[F]> for &Matrix {
    type Output = Vec<F>;

    fn mul(self, rhs: &[F]) -> Self::Output {
        self.rows
            .iter()
            .map(|row| row.iter().fold(F::ZERO, |acc, cell| acc + rhs[*cell]))
            .collect()
    }
}
