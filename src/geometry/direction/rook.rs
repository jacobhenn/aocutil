#[cfg(test)]
use crate::v;

use super::*;

use std::{
    fmt::{Debug, Write},
    mem,
    ops::{Add, AddAssign},
};

use num::Zero;

/// A "cardinal direction" in `DIM`-dimensional space.
///
/// This is implemented by simply storing the index of the axis and a sign. It
/// is a logic error for the inner number to be `>= DIM`. If a `Direction` observes such an
/// error, its behavior is unspecified.
///
/// Iteration order is currently -x +x -y +y but this may change.
///
/// Note: the `PartialOrd` implementation orders first by axis, then sign. So for 2d,
/// -x < +x < -y < +y
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RookDirection<const DIM: usize = 2> {
    axis: usize,
    sign: LineDirection,
}

impl<const DIM: usize> RookDirection<DIM> {
    pub fn new(axis: usize, sign: LineDirection) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self { axis, sign }
    }

    pub fn negative(axis: usize) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self::new(axis, LineDirection::Negative)
    }

    pub fn positive(axis: usize) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self::new(axis, LineDirection::Positive)
    }

    pub fn axis(self) -> usize {
        self.axis
    }

    pub fn sign(self) -> LineDirection {
        self.sign
    }

    pub fn with_axis(self, axis: usize) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self { axis, ..self }
    }

    pub fn with_sign(self, sign: LineDirection) -> Self {
        Self { sign, ..self }
    }

    pub fn iter() -> RookDirectionIter<DIM> {
        RookDirectionIter {
            current: Self::new(0, LineDirection::Negative),
        }
    }

    pub fn unit_vector<T>(self) -> Vector<T, DIM>
    where
        T: Neg<Output = T> + One + Zero,
    {
        Vector::from(self)
    }
}

impl<const DIM: usize> Debug for RookDirection<DIM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.sign == LineDirection::Negative {
            f.write_char('-')?;
        } else {
            f.write_char('+')?;
        }

        if self.axis < 5 {
            f.write_char(['x', 'y', 'z', 'w'][self.axis])
        } else {
            write!(f, "{}", self.axis)
        }
    }
}

impl<T, const DIM: usize> From<RookDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero,
{
    fn from(value: RookDirection<DIM>) -> Self {
        Vector::from_fn(|i| {
            if i == value.axis {
                match value.sign {
                    LineDirection::Negative => T::one().neg(),
                    LineDirection::Positive => T::one(),
                }
            } else {
                T::zero()
            }
        })
    }
}

#[test]
fn test_vector_from_rook_direction() {
    assert_eq!(
        Vector::<i32, 4>::from(RookDirection::<4>::new(2, LineDirection::Negative)),
        v!(0, 0, -1, 0)
    );
}

// TODO: this should rely on Add, not AddAssign. how do without unsafe??
impl<T, const DIM: usize> Add<RookDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero + Add,
{
    type Output = Self;

    fn add(mut self, rhs: RookDirection<DIM>) -> Self::Output {
        let old_component = mem::replace(&mut self.components[rhs.axis], T::zero());
        self.components[rhs.axis] = old_component + rhs.sign.to_num();
        self
    }
}

impl<T, const DIM: usize> AddAssign<RookDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero + AddAssign,
{
    fn add_assign(&mut self, rhs: RookDirection<DIM>) {
        self.components[rhs.axis] += rhs.sign.to_num();
    }
}

impl<const DIM: usize> Neg for RookDirection<DIM> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            sign: -self.sign,
            ..self
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RookDirectionIter<const DIM: usize> {
    current: RookDirection<DIM>,
}

impl<const DIM: usize> Iterator for RookDirectionIter<DIM> {
    type Item = RookDirection<DIM>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.axis >= DIM {
            return None;
        }

        let res = self.current;
        self.current.sign = -self.current.sign;
        if self.current.sign == LineDirection::Negative {
            self.current.axis += 1;
        }

        Some(res)
    }
}

#[test]
fn rook_direction_2_iter() {
    itertools::assert_equal(
        RookDirection::<2>::iter(),
        [
            RookDirection::<2>::MINUS_X,
            RookDirection::<2>::PLUS_X,
            RookDirection::<2>::MINUS_Y,
            RookDirection::<2>::PLUS_Y,
        ],
    );
}

#[test]
fn unit_vector() {
    itertools::assert_equal(
        RookDirection::<2>::iter().map(|d| Vector::from(d)),
        [v!(-1, 0), v!(1, 0), v!(0, -1), v!(0, 1)],
    );
}

impl RookDirection<1> {
    pub const NEGATIVE: Self = Self {
        axis: 0,
        sign: LineDirection::Negative,
    };

    pub const POSITIVE: Self = Self {
        axis: 0,
        sign: LineDirection::Positive,
    };
}

#[macro_export]
macro_rules! match_rook_direction_2d {
    (
        match $scrutinee:expr;
            -x => $mx:expr,
            +x => $px:expr,
            -y => $my:expr,
            +y => $py:expr,
    ) => {
        if $scrutinee == RookDirection::<2>::MINUS_X {
            $mx
        } else if $scrutinee == RookDirection::<2>::PLUS_X {
            $px
        } else if $scrutinee == RookDirection::<2>::MINUS_Y {
            $my
        } else if $scrutinee == RookDirection::<2>::PLUS_Y {
            $py
        } else {
            unreachable!(
                "logic error: RookDirection::<2> may not have axis {:?}",
                RookDirection::<2>::axis($scrutinee)
            )
        }
    };
}

impl RookDirection<2> {
    pub const PLUS_X: Self = Self {
        axis: 0,
        sign: LineDirection::Positive,
    };

    pub const PLUS_Y: Self = Self {
        axis: 1,
        sign: LineDirection::Positive,
    };

    pub const MINUS_X: Self = Self {
        axis: 0,
        sign: LineDirection::Negative,
    };

    pub const MINUS_Y: Self = Self {
        axis: 1,
        sign: LineDirection::Negative,
    };

    pub const fn is_horizontal(self) -> bool {
        self.axis == 0
    }

    pub const fn is_vertical(self) -> bool {
        self.axis == 1
    }

    pub fn perpendicular_axis(self) -> usize {
        (self.axis() + 1) % 2
    }

    // TODO: should i remove the positive_down from the name of this?
    /// Parse a `RookDirection<2>` from U/D/L/R using the "positive-down" convention where +y is
    /// displayed as increasing downwards.
    /// - `"U" => Self::MINUS_Y`
    /// - `"D" => Self::PLUS_Y`
    /// - `"L" => Self::MINUS_X`
    /// - `"R" => Self::PLUS_X`
    pub fn from_udlr_positive_down(c: &str) -> Option<Self> {
        match c {
            "U" => Some(Self::MINUS_Y),
            "D" => Some(Self::PLUS_Y),
            "L" => Some(Self::MINUS_X),
            "R" => Some(Self::PLUS_X),
            _ => None,
        }
    }

    /// Parse a `RookDirection<2>` from ^/v/</> using the "positive-down" convention where +y is
    /// displayed as increasing downwards.
    /// - `"^" => Self::MINUS_Y`
    /// - `"v" => Self::PLUS_Y`
    /// - `"<" => Self::MINUS_X`
    /// - `">" => Self::PLUS_X`
    pub fn from_ascii_arrow(c: char) -> Option<Self> {
        match c {
            '^' => Some(Self::MINUS_Y),
            'v' => Some(Self::PLUS_Y),
            '<' => Some(Self::MINUS_X),
            '>' => Some(Self::PLUS_X),
            _ => None,
        }
    }

    pub fn to_ascii_arrow(self) -> char {
        match_rook_direction_2d! {
            match self;
                -x => '<',
                +x => '>',
                -y => '^',
                +y => 'v',
        }
    }

    // pub fn from_nesw(c: &str) -> Option<Self> {
    //     match c {
    //         "N" => Some(Self::NORTH),
    //         "E" => Some(Self::EAST),
    //         "S" => Some(Self::SOUTH),
    //         "W" => Some(Self::WEST),
    //         _ => None,
    //     }
    // }
}
