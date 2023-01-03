use crate::v;

use std::{
    iter,
    ops::{Index, IndexMut},
};

use super::vector::Vector;

/// A `DIM`-dimensional grid of values. It is unspecified behavior for `values` to have a length
/// that is not the product of `self.dimensions`, and so that should be impossible to achieve by
/// interacting with this through the public interface.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Grid<T, const DIM: usize = 2> {
    dimensions: [usize; DIM],
    values: Vec<T>,
}

impl<T, const DIM: usize> Grid<T, DIM> {
    pub fn new() -> Self {
        Self {
            dimensions: [0; DIM],
            values: Vec::new(),
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

    fn unfold_pos(&self, pos: GridPos<DIM>) -> Option<usize> {
        let mut i = 0;
        let mut coef = 1;
        for (index, dimension) in iter::zip(pos.components, self.dimensions) {
            let index = usize::try_from(index).ok()?;

            i += coef * index;
            coef *= dimension;
        }

        Some(i)
    }

    pub fn contains_pos(&self, pos: GridPos<DIM>) -> bool {
        iter::zip(self.dimensions, pos.components)
            .all(|(dim, cmp)| usize::try_from(cmp).map(|cmp| cmp < dim).unwrap_or(false))
    }

    pub fn get(&self, pos: GridPos<DIM>) -> Option<&T> {
        self.contains_pos(pos)
            .then(|| self.unfold_pos(pos).and_then(|pos| self.values.get(pos)))
            .flatten()
    }

    pub fn get_mut(&mut self, pos: GridPos<DIM>) -> Option<&mut T> {
        self.contains_pos(pos)
            .then(|| {
                self.unfold_pos(pos)
                    .and_then(|pos| self.values.get_mut(pos))
            })
            .flatten()
    }

    pub fn neighbors(&self, center: GridPos<DIM>) -> Neighbors<'_, T, DIM> {
        println!("making neighbors at {center}");
        Neighbors {
            grid: self,
            center,
            offset: v!(-1; DIM),
            idx: 0,
        }
    }
}

impl<T> Grid<T, 2> {
    pub fn rows(&self) -> impl Iterator<Item = &[T]> {
        self.values.windows(self.dimension(0))
    }

    pub fn columns(&self) -> impl Iterator<Item = impl Iterator<Item = &T>> {
        (0..self.dimension(0)).map(move |column| {
            (0..self.dimension(1)).map(move |row| &self[v!(row as isize, column as isize)])
        })
    }
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
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
    ]
    .into_iter()
    .collect();
    assert_eq!(grid[v!(0, 0)], 1);
    assert_eq!(grid[v!(2, 0)], 3);
    assert_eq!(grid[v!(0, 2)], 7);
    assert_eq!(grid[v!(2, 2)], 9);
}

#[derive(Copy, Clone)]
pub struct Neighbors<'a, T, const DIM: usize> {
    grid: &'a Grid<T, DIM>,
    center: GridPos<DIM>,
    offset: GridPos<DIM>,
    idx: usize,
}

impl<'a, T, const DIM: usize> Neighbors<'a, T, DIM> {
    fn inc_offset(&mut self) {
        let mut carry = true;
        for component in self.offset.components.iter_mut() {
            if !carry {
                break;
            }

            if *component == 2 {
                *component = 0;
                carry = true;
            } else {
                *component += 1;
                carry = false;
            }
        }

        self.idx += 1;
    }
}

impl<'a, T, const DIM: usize> Iterator for Neighbors<'a, T, DIM> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        println!(
            "currently on {} (pos: {}) (idx: {})",
            self.offset,
            self.center + self.offset,
            self.idx,
        );
        let last_offset = self.offset;
        self.inc_offset();
        if self.idx > 9 {
            return None;
        }

        if last_offset.components.iter().all(|&c| c == 0) {
            println!("    skipping (center)");
            return self.next();
        }

        self.grid.get(self.center + last_offset).or_else(|| {
            println!("    skipping (oob)");
            self.next()
        })
    }
}

#[test]
fn test_neighbors() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![3, 5, 2],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![4, 5, 8],
    ]
    .into_iter()
    .collect();

    let mut neighbors = grid.neighbors(v!(1, 1));
    assert_eq!(neighbors.next(), Some(&1));
    assert_eq!(neighbors.next(), Some(&2));
    assert_eq!(neighbors.next(), Some(&3));
    assert_eq!(neighbors.next(), Some(&3));
    assert_eq!(neighbors.next(), Some(&2));
    assert_eq!(neighbors.next(), Some(&4));
    assert_eq!(neighbors.next(), Some(&5));
    assert_eq!(neighbors.next(), Some(&6));
    assert_eq!(neighbors.next(), None);
}

#[test]
fn test_corner_neighbors() {
    let grid: Grid<_, 2> = vec![
        vec![1, 2, 3],
        vec![3, 5, 2],
        vec![4, 5, 6],
        vec![7, 8, 9],
        vec![4, 5, 8],
    ]
    .into_iter()
    .collect();

    let mut neighbors = grid.neighbors(v!(0, 2));
    assert_eq!(neighbors.next(), Some(&2));
    assert_eq!(neighbors.next(), Some(&5));
    assert_eq!(neighbors.next(), Some(&2));
    assert_eq!(neighbors.next(), None);
}
