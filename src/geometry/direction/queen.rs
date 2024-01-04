use std::{
    fmt::Debug,
    ops::{Add, AddAssign},
};

use super::*;

use num::Zero;

/// The canonical order of queen directions is that of bishop directions chained with that of rook
/// directions. So in 2d, `[-x -y] < [+x -y] < [-x +y] < [+x +y] < [-x] < [+x] < [-y] < [+y]`.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone)]
pub enum QueenDirection<const DIM: usize> {
    Bishop(BishopDirection<DIM>),
    Rook(RookDirection<DIM>),
}

impl<const DIM: usize> Debug for QueenDirection<DIM> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QueenDirection::Bishop(b) => write!(f, "{b:?}"),
            QueenDirection::Rook(r) => write!(f, "[{r:?}]"),
        }
    }
}

#[test]
fn test_debug() {
    assert_eq!(format!("{:?}", QueenDirection::MINUS_PLUS), "[-x +y]");
    assert_eq!(format!("{:?}", QueenDirection::PLUS_X), "[+x]");
}

impl<const DIM: usize> QueenDirection<DIM> {
    pub fn iter() -> impl Iterator<Item = Self> {
        Iterator::chain(
            BishopDirection::<DIM>::iter().map(Self::Bishop),
            RookDirection::<DIM>::iter().map(Self::Rook),
        )
    }

    pub fn unit_vector<T>(self) -> Vector<T, DIM>
    where
        T: Neg<Output = T> + One + Zero,
    {
        match self {
            QueenDirection::Bishop(b) => b.unit_vector(),
            QueenDirection::Rook(r) => r.unit_vector(),
        }
    }
}

impl<T, const DIM: usize> From<QueenDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero,
{
    fn from(value: QueenDirection<DIM>) -> Self {
        value.unit_vector()
    }
}

impl<T, const DIM: usize> Add<QueenDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero + Add,
{
    type Output = Vector<<T as Add>::Output, DIM>;

    fn add(self, rhs: QueenDirection<DIM>) -> Self::Output {
        self + rhs.unit_vector()
    }
}

impl<T, const DIM: usize> AddAssign<QueenDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero + AddAssign,
{
    fn add_assign(&mut self, rhs: QueenDirection<DIM>) {
        *self += rhs.unit_vector();
    }
}

impl QueenDirection<2> {
    pub const MINUS_MINUS: Self = Self::Bishop(BishopDirection::MINUS_MINUS);
    pub const PLUS_MINUS: Self = Self::Bishop(BishopDirection::PLUS_MINUS);
    pub const MINUS_PLUS: Self = Self::Bishop(BishopDirection::MINUS_PLUS);
    pub const PLUS_PLUS: Self = Self::Bishop(BishopDirection::PLUS_PLUS);

    pub const MINUS_X: Self = Self::Rook(RookDirection::MINUS_X);
    pub const PLUS_X: Self = Self::Rook(RookDirection::PLUS_X);
    pub const MINUS_Y: Self = Self::Rook(RookDirection::MINUS_Y);
    pub const PLUS_Y: Self = Self::Rook(RookDirection::PLUS_Y);
}

#[test]
fn test_iter() {
    itertools::assert_equal(
        QueenDirection::iter(),
        [
            QueenDirection::MINUS_MINUS,
            QueenDirection::PLUS_MINUS,
            QueenDirection::MINUS_PLUS,
            QueenDirection::PLUS_PLUS,
            QueenDirection::MINUS_X,
            QueenDirection::PLUS_X,
            QueenDirection::MINUS_Y,
            QueenDirection::PLUS_Y,
        ],
    )
}
