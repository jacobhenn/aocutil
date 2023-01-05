use std::{
    cmp::{self, Ordering},
    fmt::Debug,
};

/// Discretely ordered types.
pub trait DiscreteOrd: PartialOrd {
    /// Returns `true` if there does not exist any term `x` of this type such that
    /// `x > self && x < rhs`.
    fn abuts(&self, rhs: &Self) -> bool;
}

macro_rules! int_discrete_ord_impl {
    { $($t:ty)+ } => {
        $(
            impl DiscreteOrd for $t {
                fn abuts(&self, rhs: &Self) -> bool {
                    self.abs_diff(*rhs) == 1
                }
            }
        )+
    }
}

int_discrete_ord_impl! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

/// This implementation is probably nonsensical for non-finite values but who cares!
macro_rules! float_discrete_ord_impl {
    { $($t:ty)+ } => {
        $(
            impl DiscreteOrd for $t {
                fn abuts(&self, rhs: &Self) -> bool {
                    self.to_bits().abuts(&rhs.to_bits())
                }
            }
        )+
    }
}

float_discrete_ord_impl! { f32 f64 }

/// An inclusive range representing all values `x: T` such that
/// `x >= range.start && x <= range.end`
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct Range<T> {
    pub start: T,
    pub end: T,
}

pub trait AsBounds<T> {
    fn start(&self) -> &T;
    fn end(&self) -> &T;
}

impl<T> AsBounds<T> for T {
    fn start(&self) -> &T {
        self
    }

    fn end(&self) -> &T {
        self
    }
}

impl<T> AsBounds<T> for Range<T> {
    fn start(&self) -> &T {
        &self.start
    }

    fn end(&self) -> &T {
        &self.end
    }
}

impl<T> Range<T> {
    pub fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    /// Creates a range between the smaller of `a` and `b` to the larger. If there is no ordering
    /// between them, returns `None`.
    pub fn partial_ordered(a: T, b: T) -> Option<Self>
    where
        T: PartialOrd,
    {
        a.partial_cmp(&b).map(|ordering| match ordering {
            Ordering::Less | Ordering::Equal => Self::new(a, b),
            Ordering::Greater => Self::new(b, a),
        })
    }

    /// Creates a range between the smaller of `a` and `b` to the larger.
    pub fn ordered(a: T, b: T) -> Self
    where
        T: Ord,
    {
        if a < b {
            Self::new(a, b)
        } else {
            Self::new(b, a)
        }
    }

    /// Creates a range containing only `val`.
    pub fn singleton(val: T) -> Self
    where
        T: Clone,
    {
        Self {
            start: val.clone(),
            end: val,
        }
    }

    /// Tests if this range contains the value `val`.
    pub fn contains(&self, val: &T) -> bool
    where
        T: PartialOrd,
    {
        val >= &self.start && val <= &self.end
    }

    /// Tests if this range intersects `other` (that is, if there exists some x such that
    /// `self.contains(&x) && other.contains(&x)`).
    pub fn intersects(&self, other: &impl AsBounds<T>) -> bool
    where
        T: PartialOrd,
    {
        (&self.start <= other.end() && &self.end >= other.start())
            || (other.start() <= &self.end && other.end() >= &self.start)
    }

    /// Tests if this range and `other` touch - that is, if `self.start..=other.end` is the exact
    /// union of `self` and `other`.
    pub fn touches(&self, other: &impl AsBounds<T>) -> bool
    where
        T: DiscreteOrd,
    {
        (&self.start <= other.end()
            && (&self.end >= other.start() || self.end.abuts(other.start())))
            || (other.start() <= &self.end
                && (other.end() >= &self.start || other.end().abuts(&self.start)))
    }

    /// Returns the smallest range which is a superset of `self` and `other`.
    pub fn hull(self, other: Self) -> Self
    where
        T: Ord,
    {
        Self::new(
            cmp::min(self.start, other.start),
            cmp::max(self.end, other.end),
        )
    }

    /// Returns a new range with the given function applied to the start and end.
    pub fn map<U, F>(self, f: F) -> Range<U>
    where
        F: Fn(T) -> U,
    {
        Range {
            start: f(self.start),
            end: f(self.end),
        }
    }
}

impl<T> Debug for Range<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:?}..{:?}]", self.start, self.end)
    }
}

impl<T> From<std::ops::RangeInclusive<T>> for Range<T> {
    fn from(value: std::ops::RangeInclusive<T>) -> Self {
        let (start, end) = value.into_inner();
        Self { start, end }
    }
}

impl<T> From<T> for Range<T>
where
    T: Clone,
{
    fn from(value: T) -> Self {
        Self::singleton(value)
    }
}
