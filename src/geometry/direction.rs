use super::*;

use std::ops::Neg;

use num::One;

pub mod rook;

pub mod bishop;

pub mod queen;

pub use rook::*;

pub use bishop::*;

pub use queen::*;

/// Note: PartialOrd is Negative < Positive
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy, PartialOrd, Ord)]
#[repr(u8)]
pub enum LineDirection {
    Negative,
    Positive,
}

impl LineDirection {
    pub fn to_num<T>(self) -> T
    where
        T: One + Neg<Output = T>,
    {
        match self {
            LineDirection::Negative => -T::one(),
            LineDirection::Positive => T::one(),
        }
    }

    /// Returns `true` if the line direction is [`Negative`].
    ///
    /// [`Negative`]: LineDirection::Negative
    #[must_use]
    pub fn is_negative(&self) -> bool {
        matches!(self, Self::Negative)
    }

    /// Returns `true` if the line direction is [`Positive`].
    ///
    /// [`Positive`]: LineDirection::Positive
    #[must_use]
    pub fn is_positive(&self) -> bool {
        matches!(self, Self::Positive)
    }
}

impl Neg for LineDirection {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            LineDirection::Negative => LineDirection::Positive,
            LineDirection::Positive => LineDirection::Negative,
        }
    }
}

impl From<RookDirection<1>> for LineDirection {
    fn from(value: RookDirection<1>) -> Self {
        value.sign()
    }
}
