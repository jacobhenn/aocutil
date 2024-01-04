use crate::{
    geometry::{BishopDirection, LineDirection, RookDirection, Vector},
    v,
};

use std::{
    iter,
    ops::{Index, IndexMut},
};

/// A `DIM`-dimensional grid of values.
///
/// # UNIFIED ORIENTATION CONVENTIONS
///
/// TODO
///
// It is unspecified behavior for `values` to have a length
// that is not the product of `self.dimensions`, and so that should be impossible to achieve by
// interacting with this through the public interface.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Grid<T, const DIM: usize = 2> {
    dimensions: [usize; DIM],
    values: Vec<T>,
}

impl<T, const DIM: usize> Grid<T, DIM> {
    /// Creates an empty `Grid`.
    pub fn new() -> Self {
        Self {
            dimensions: [0; DIM],
            values: Vec::new(),
        }
    }

    /// Creates a new `Grid` with the given dimensions and fills it with copies of the provided
    /// value.
    pub fn from_dims_and_val(dimensions: [usize; DIM], val: T) -> Self
    where
        T: Copy,
    {
        Self {
            dimensions,
            values: vec![val; dimensions.into_iter().product()],
        }
    }

    pub fn dimensions(&self) -> [usize; DIM] {
        self.dimensions
    }

    pub fn values(&self) -> &[T] {
        &self.values
    }

    pub fn into_values(self) -> Vec<T> {
        self.values
    }

    pub fn dimension(&self, dim: usize) -> usize {
        self.dimensions[dim]
    }

    pub fn fold_pos(&self, pos: GridPos<DIM>) -> Option<usize> {
        let mut i = 0;
        let mut coef = 1;
        for (index, dimension) in iter::zip(pos.components, self.dimensions) {
            let index = usize::try_from(index).ok()?;

            i += coef * index;
            coef *= dimension;
        }

        Some(i)
    }

    pub fn unfold_pos(&self, mut pos: usize) -> GridPos<DIM> {
        let mut res = v!(0; DIM);
        for (index, dimension) in iter::zip(&mut res.components, self.dimensions) {
            *index = (pos % dimension) as isize;
            pos /= dimension;
        }

        res
    }

    pub fn contains_pos(&self, pos: GridPos<DIM>) -> bool {
        iter::zip(self.dimensions, pos.components)
            .all(|(dim, cmp)| usize::try_from(cmp).map(|cmp| cmp < dim).unwrap_or(false))
    }

    pub fn get(&self, pos: GridPos<DIM>) -> Option<&T> {
        self.contains_pos(pos)
            .then(|| self.fold_pos(pos).and_then(|pos| self.values.get(pos)))
            .flatten()
    }

    pub fn get_mut(&mut self, pos: GridPos<DIM>) -> Option<&mut T> {
        self.contains_pos(pos)
            .then(|| self.fold_pos(pos).and_then(|pos| self.values.get_mut(pos)))
            .flatten()
    }

    /// Get the value at `pos` in this grid. If the position lies outside the grid, treat the
    /// grid like it repeats infinitely in every direction.
    pub fn get_wrapping(&self, mut pos: GridPos<DIM>) -> &T {
        for i in 0..DIM {
            pos[i] = pos[i].rem_euclid(self.dimensions[i] as isize);
        }

        self.get(pos)
            .expect("wrapped position should be inside array")
    }

    /// Swaps two values in the grid.
    ///
    /// # Panics
    /// Panics if `p` or `q` are out of bounds.
    pub fn swap(&mut self, p: GridPos<DIM>, q: GridPos<DIM>) {
        let i = self
            .fold_pos(p)
            .expect("positions to swap should be inside array");
        let j = self
            .fold_pos(q)
            .expect("positions to swap should be inside array");

        self.values.swap(i, j);
    }

    pub fn rook_neighbors(&self, center: GridPos<DIM>) -> impl Iterator<Item = &T> {
        RookDirection::<DIM>::iter().filter_map(move |d| self.get(center + d))
    }

    pub fn rook_neighbor_positions<'a>(
        &'a self,
        center: GridPos<DIM>,
    ) -> impl Iterator<Item = GridPos<DIM>> + 'a {
        RookDirection::<DIM>::iter()
            .map(move |d| center + d)
            .filter(|&n| self.contains_pos(n))
    }

    // TODO: rename this to rook_neighbors_with_pos or something
    pub fn enumerated_rook_neighbors(
        &self,
        center: GridPos<DIM>,
    ) -> impl Iterator<Item = (GridPos<DIM>, &T)> {
        RookDirection::<DIM>::iter().filter_map(move |d| {
            let n = center + d;
            self.get(n).map(|v| (n, v))
        })
    }

    pub fn bishop_neighbors(&self, center: GridPos<DIM>) -> impl Iterator<Item = &T> {
        BishopDirection::<DIM>::iter().filter_map(move |d| self.get(center + d))
    }

    pub fn bishop_neighbor_positions<'a>(
        &'a self,
        center: GridPos<DIM>,
    ) -> impl Iterator<Item = GridPos<DIM>> + 'a {
        BishopDirection::<DIM>::iter()
            .map(move |d| center + d)
            .filter(|&n| self.contains_pos(n))
    }

    pub fn enumerated_bishop_neighbors(
        &self,
        center: GridPos<DIM>,
    ) -> impl Iterator<Item = (GridPos<DIM>, &T)> {
        BishopDirection::<DIM>::iter().filter_map(move |d| {
            let n = center + d;
            self.get(n).map(|v| (n, v))
        })
    }

    /// Returns the maximum distance you could travel from `pos` in `direction` while staying
    /// inside the dimensions of the grid.
    pub fn distance_to_edge(&self, pos: GridPos<DIM>, direction: RookDirection<DIM>) -> isize {
        match direction.sign() {
            LineDirection::Negative => pos[direction.axis()],
            LineDirection::Positive => {
                self.dimensions[direction.axis()] as isize - pos[direction.axis()] - 1
            }
        }
    }

    pub fn find(&self, f: impl FnMut(&T) -> bool) -> Option<GridPos<DIM>> {
        self.values.iter().position(f).map(|i| self.unfold_pos(i))
    }

    /// Returns an iterator over the lattice points contained in this grid.
    ///
    /// "zm" stands for "zero major", so the iterator will increment dimension `0` contiguously
    /// (in 2d, this means row-major)
    pub fn positions_zm(&self) -> Positions<DIM> {
        Positions {
            dimensions: self.dimensions,
            current: v!(0; DIM),
            carry: false,
        }
    }

    /// "zm" stands for "zero major", so the iterator will increment dimension `0` contiguously
    /// (in 2d, this means row-major)
    pub fn iter_zm_mut_with_pos(&mut self) -> impl Iterator<Item = (GridPos<DIM>, &mut T)> {
        self.positions_zm().zip(self.values.iter_mut())
    }

    /// "zm" stands for "zero major", so the iterator will increment dimension `0` contiguously
    /// (in 2d, this means row-major)
    pub fn iter_zm_with_pos(&self) -> impl Iterator<Item = (GridPos<DIM>, &T)> {
        self.positions_zm().zip(self.values.iter())
    }
}

#[test]
fn test_fold_unfold_pos() {
    let grid = Grid::<i32, 8> {
        dimensions: [78, 32, 10, 500, 4, 67, 40, 36],
        values: Vec::new(),
    };
    let v = v!(9, 4, 3, 87, 2, 47, 20, 30);
    assert_eq!(grid.unfold_pos(grid.fold_pos(v).unwrap()), v);

    let n = 65465416;
    assert_eq!(grid.fold_pos(grid.unfold_pos(n)).unwrap(), n);
}

#[test]
fn test_get_wrapping() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![10, 11, 12],
        vec![13, 14, 15],
    ]
    .into_iter()
    .collect();

    assert_eq!(*grid.get_wrapping(v!(1, 1)), 5);
    assert_eq!(*grid.get_wrapping(v!(4, 1)), 5);
    assert_eq!(*grid.get_wrapping(v!(-2, 1)), 5);
    assert_eq!(*grid.get_wrapping(v!(1, -4)), 5);
    assert_eq!(*grid.get_wrapping(v!(-2, -4)), 5);
    assert_eq!(*grid.get_wrapping(v!(-14, -14)), 5);
}

#[test]
fn test_find() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![10, 11, 12],
        vec![13, 14, 15],
    ]
    .into_iter()
    .collect();

    assert_eq!(grid.find(|&x| x == 11).unwrap(), v!(1, 3));
}

#[test]
fn test_cardinal_neighbors() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![10, 11, 12],
        vec![13, 14, 15],
    ]
    .into_iter()
    .collect();

    itertools::assert_equal(grid.rook_neighbors(v!(1, 1)), [&4, &6, &2, &8]);
}

#[test]
fn test_corner_cardinal_neighbors() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![10, 11, 12],
        vec![13, 14, 15],
    ]
    .into_iter()
    .collect();

    itertools::assert_equal(grid.rook_neighbors(v!(2, 4)), [&14, &12]);
}

impl<T> Grid<T, 2> {
    pub fn width(&self) -> usize {
        self.dimensions[0]
    }

    pub fn height(&self) -> usize {
        self.dimensions[1]
    }

    pub fn rows(&self) -> impl Iterator<Item = &[T]> {
        self.values.chunks(self.dimension(0))
    }

    pub fn columns(&self) -> impl Iterator<Item = impl Iterator<Item = &T>> {
        (0..self.dimension(0)).map(move |column| {
            (0..self.dimension(1)).map(move |row| &self[v!(column as isize, row as isize)])
        })
    }

    pub fn push_row<I>(&mut self, row: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.values.extend(row);
        self.dimensions[1] += 1;
        assert_eq!(self.values.len(), self.dimensions[0] * self.dimensions[1]);
    }

    // TODO: this is highly inefficient. think about different ways to do this
    pub fn insert_row<I>(&mut self, y: usize, new_row: I)
    where
        I: IntoIterator<Item = T>,
    {
        let mut i = self
            .fold_pos(v!(0, y as isize))
            .expect("row should be within bounds");

        for value in new_row {
            self.values.insert(i, value);
            i += 1;
        }

        self.dimensions[1] += 1;
        assert_eq!(self.values.len(), self.dimensions[0] * self.dimensions[1]);
    }

    #[must_use]
    pub fn render(&self, render_val: impl Fn(GridPos, &T) -> char) -> String {
        let mut res = String::with_capacity((self.width() + 1) * self.height());
        for (y, row) in self.rows().enumerate() {
            for (x, val) in row.iter().enumerate() {
                res.push(render_val(v!(x as isize, y as isize), val));
            }
            res.push('\n');
        }

        res
    }

    pub fn transposed(&self) -> Self
    where
        T: Clone,
    {
        self.columns().map(Iterator::cloned).collect()
    }
}

#[test]
fn test_columns() {
    let grid: Grid<i32, 2> = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]
        .into_iter()
        .collect();

    let middle_column: Vec<i32> = grid.columns().nth(1).unwrap().copied().collect();
    assert_eq!(middle_column, vec![2, 5, 8]);
}

#[test]
fn test_transposed() {
    let grid: Grid<i32, 2> = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]
        .into_iter()
        .collect();

    let grid_transposed: Grid<i32, 2> = vec![vec![1, 4, 7], vec![2, 5, 8], vec![3, 6, 9]]
        .into_iter()
        .collect();

    assert_eq!(grid.transposed(), grid_transposed);
}

#[test]
fn test_insert_row() {
    let mut before: Grid<_, 2> = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]
        .into_iter()
        .collect();

    let after: Grid<_, 2> = vec![vec![1, 2, 3], vec![0, 0, 0], vec![4, 5, 6], vec![7, 8, 9]]
        .into_iter()
        .collect();

    before.insert_row(1, vec![0, 0, 0]);

    assert_eq!(before, after);
}

impl<R, T> FromIterator<R> for Grid<T, 2>
where
    R: IntoIterator<Item = T>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = R>,
    {
        let mut res = Self::new();
        let mut rows = iter.into_iter();
        if let Some(row) = rows.next() {
            res.values.extend(row);
            res.dimensions[0] = res.values.len();
        }

        for row in rows {
            res.values.extend(row);
        }

        let height = res.values.len() / res.dimensions[0];
        assert_eq!(
            res.dimensions[0] * height,
            res.values.len(),
            "grid rows must have equal length"
        );

        res.dimensions[1] = height;
        res
    }
}

#[test]
fn test_grid_from_iterator() {
    let grid: Grid<_> = vec![vec![1, 2, 3], vec![7, 8, 9], vec![4, 5, 6]]
        .into_iter()
        .collect();
    assert_eq!(grid.dimensions, [3, 3]);
    assert_eq!(grid.values, [1, 2, 3, 7, 8, 9, 4, 5, 6]);
}

#[test]
#[should_panic]
fn test_bad_grid_from_iterator() {
    let _: Grid<_> = vec![vec![1, 2, 3], vec![7, 8, 9, 10], vec![4, 5, 6]]
        .into_iter()
        .collect();
}

/// A position in a grid, represented as a vector of components in **reverse indexing order**, so
/// in a traditional multidimensional array, grid\[v!(a, b, c)\] would equal grid\[c\]\[b\]\[a\].
/// In other words, **(column, row)**.
pub type GridPos<const DIM: usize = 2> = Vector<isize, DIM>;

impl<T, const DIM: usize> Index<GridPos<DIM>> for Grid<T, DIM> {
    type Output = T;

    fn index(&self, pos: GridPos<DIM>) -> &Self::Output {
        self.get(pos)
            .ok_or_else(|| format!("grid position {pos} out of bounds"))
            .unwrap()
    }
}

impl<T, const DIM: usize> IndexMut<GridPos<DIM>> for Grid<T, DIM> {
    fn index_mut(&mut self, pos: GridPos<DIM>) -> &mut Self::Output {
        self.get_mut(pos)
            .ok_or_else(|| format!("grid position {pos} out of bounds"))
            .unwrap()
    }
}

#[test]
fn test_grid_idx() {
    let grid: Grid<_, 2> = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]
        .into_iter()
        .collect();
    assert_eq!(grid[v!(0, 0)], 1);
    assert_eq!(grid[v!(2, 0)], 3);
    assert_eq!(grid[v!(0, 2)], 7);
    assert_eq!(grid[v!(2, 2)], 9);
}

pub struct Positions<const DIM: usize> {
    dimensions: [usize; DIM],
    current: GridPos<DIM>,
    carry: bool,
}

impl<const DIM: usize> Iterator for Positions<DIM> {
    type Item = GridPos<DIM>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.carry {
            return None;
        }

        let res = self.current;
        self.carry = true;
        for (component, dimension) in iter::zip(&mut self.current.components, self.dimensions) {
            if self.carry {
                *component += 1;
            }

            if *component == dimension as isize {
                *component = 0;
            } else {
                self.carry = false;
            }
        }

        Some(res)
    }
}

#[test]
fn test_positions() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![10, 11, 12],
        vec![13, 14, 15],
    ]
    .into_iter()
    .collect();

    let mut positions = grid.positions_zm();
    assert_eq!(positions.next(), Some(v!(0, 0)));
    assert_eq!(positions.nth(4), Some(v!(2, 1)));
    assert_eq!(positions.nth(4), Some(v!(1, 3)));
    assert_eq!(positions.nth(2), Some(v!(1, 4)));
    assert_eq!(positions.next(), Some(v!(2, 4)));
    assert_eq!(positions.next(), None);
}
