use crate::{ArrayCounter, Endianness};

use super::*;

use std::{
    cmp::Ordering,
    fmt::Debug,
    iter,
    ops::{Add, AddAssign},
};

/// The `Ord` order is lexicographic on the signs in each axis ordered by dimension. So for 2d,
/// `[-x -y] < [+x -y] < [-x +y] < [+x +y]`
#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct BishopDirection<const DIM: usize = 2> {
    pub components: [LineDirection; DIM],
}

impl<const DIM: usize> Debug for BishopDirection<DIM> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut it = iter::zip(AXES, self.components.iter()).peekable();
        while let Some((axis, direction)) = it.next() {
            match direction {
                LineDirection::Negative => write!(f, "-")?,
                LineDirection::Positive => write!(f, "+")?,
            }

            write!(f, "{axis}")?;

            if it.peek().is_some() {
                write!(f, " ")?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

#[test]
fn test_debug() {
    assert_eq!(format!("{:?}", BishopDirection::MINUS_PLUS), "[-x +y]");
}

impl<const DIM: usize> PartialOrd for BishopDirection<DIM> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const DIM: usize> Ord for BishopDirection<DIM> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in iter::zip(&self.components, &other.components).rev() {
            if a != b {
                return a.cmp(b);
            }
        }

        Ordering::Equal
    }
}

#[test]
fn test_bishop_direction_order() {
    assert!(BishopDirection::MINUS_MINUS < BishopDirection::PLUS_MINUS);
    assert!(BishopDirection::PLUS_MINUS < BishopDirection::MINUS_PLUS);
    assert!(BishopDirection::MINUS_PLUS < BishopDirection::PLUS_PLUS);
}

impl<const DIM: usize> BishopDirection<DIM> {
    pub const fn new(components: [LineDirection; DIM]) -> Self {
        Self { components }
    }

    pub fn iter() -> impl Iterator<Item = Self> {
        ArrayCounter::<DIM>::new(Endianness::Little, 2).map(|arr| {
            Self::new(arr.map(|n| match n {
                0 => LineDirection::Negative,
                1 => LineDirection::Positive,
                _ => panic!("array counter out of range"),
            }))
        })
    }

    pub fn unit_vector<T>(self) -> Vector<T, DIM>
    where
        T: One + Neg<Output = T>,
    {
        Vector::<T, DIM>::new(self.components.map(LineDirection::to_num))
    }
}

impl<T, const DIM: usize> From<BishopDirection<DIM>> for Vector<T, DIM>
where
    T: One + Neg<Output = T>,
{
    fn from(value: BishopDirection<DIM>) -> Self {
        value.unit_vector()
    }
}

impl<T, const DIM: usize> Add<BishopDirection<DIM>> for Vector<T, DIM>
where
    T: One + Neg<Output = T> + Add<T>,
{
    type Output = Vector<<T as Add<T>>::Output, DIM>;

    fn add(self, rhs: BishopDirection<DIM>) -> Self::Output {
        self + rhs.unit_vector()
    }
}

impl<T, const DIM: usize> AddAssign<BishopDirection<DIM>> for Vector<T, DIM>
where
    T: One + Neg<Output = T> + AddAssign,
{
    fn add_assign(&mut self, rhs: BishopDirection<DIM>) {
        *self += rhs.unit_vector();
    }
}

#[test]
fn test_iter() {
    for dir in BishopDirection::<2>::iter() {
        println!("{dir:?}");
    }

    itertools::assert_equal(
        BishopDirection::<2>::iter(),
        [
            BishopDirection::MINUS_MINUS,
            BishopDirection::PLUS_MINUS,
            BishopDirection::MINUS_PLUS,
            BishopDirection::PLUS_PLUS,
        ],
    );
}

impl BishopDirection<2> {
    pub const MINUS_MINUS: Self = Self::new([LineDirection::Negative, LineDirection::Negative]);
    pub const PLUS_MINUS: Self = Self::new([LineDirection::Positive, LineDirection::Negative]);
    pub const MINUS_PLUS: Self = Self::new([LineDirection::Negative, LineDirection::Positive]);
    pub const PLUS_PLUS: Self = Self::new([LineDirection::Positive, LineDirection::Positive]);
}

#[cfg(test)]
use crate::v;

#[test]
fn bishop_direction_to_vector() {
    assert_eq!(
        Into::<Vector<i32>>::into(BishopDirection::<2>::MINUS_PLUS),
        v!(-1, 1)
    );
}
