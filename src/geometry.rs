pub mod vector;

pub mod direction;

pub mod rotation;

pub mod metric;

use std::fmt::{self, Display};

pub use vector::*;

pub use direction::*;

pub use rotation::*;

pub use metric::Metric;

pub const AXES: &[char] = &['x', 'y', 'z', 'w'];

pub const BASIS_LETTERS: &[char] = &['i', 'j', 'k', 'l'];

// TODO: remove this?
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PlaneAxis {
    Horizontal,
    Vertical,
}

impl PlaneAxis {
    pub fn iter() -> impl Iterator<Item = Self> {
        [Self::Horizontal, Self::Vertical].into_iter()
    }

    pub fn other(self) -> Self {
        match self {
            PlaneAxis::Horizontal => PlaneAxis::Vertical,
            PlaneAxis::Vertical => PlaneAxis::Horizontal,
        }
    }
}

impl Display for PlaneAxis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PlaneAxis::Horizontal => f.write_str("horizontal"),
            PlaneAxis::Vertical => f.write_str("vertical"),
        }
    }
}
