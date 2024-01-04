use std::{
    cmp::{self, Ordering},
    fmt::Debug,
    ops::Sub,
};

pub mod multi;

/// Discretely ordered types.
// TODO: replace with `iter::Step` once that's stabilized
pub trait DiscreteOrd: PartialOrd + Sized {
    fn successor(self) -> Self;

    fn predecessor(self) -> Self;

    fn abuts(&self, other: &Self) -> bool;
}

macro_rules! int_discrete_ord_impl {
    { $($t:ty)+ } => {
        $(
            impl DiscreteOrd for $t {
                fn successor(self) -> Self { self + 1 }

                fn predecessor(self) -> Self { self - 1 }

                fn abuts(&self, other: &Self) -> bool {
                    self.abs_diff(*other) == 1
                }
            }
        )+
    }
}

int_discrete_ord_impl! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

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

impl<T> AsBounds<T> for Range<&T> {
    fn start(&self) -> &T {
        self.start
    }

    fn end(&self) -> &T {
        self.end
    }
}

impl<T> AsBounds<T> for std::ops::RangeInclusive<T> {
    fn start(&self) -> &T {
        self.start()
    }

    fn end(&self) -> &T {
        self.end()
    }
}

impl<T> Range<T> {
    pub fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    pub fn is_empty(&self) -> bool
    where
        T: PartialOrd,
    {
        self.start > self.end
    }

    // TODO: how should this handle empty ranges?
    /// For ranges of discrete values, returns how many values are contained.
    ///
    /// # Examples
    ///
    /// ```
    /// use aocutil::range::Range;
    ///
    /// assert_eq!(Range::new(0, 6).len(), 7);
    /// assert_eq!(Range::new(6, 0).len(), 0);
    /// ```
    pub fn len(self) -> T
    where
        T: Sub<T, Output = T> + num::Zero + DiscreteOrd,
    {
        if self.is_empty() {
            return T::zero();
        }

        (self.end - self.start).successor()
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
    pub fn contains(&self, val: &impl AsBounds<T>) -> bool
    where
        T: PartialOrd,
    {
        val.start() >= &self.start && val.end() <= &self.end
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

    pub fn intersection(self, other: Self) -> Self
    where
        T: Ord,
    {
        Self::new(
            cmp::max(self.start, other.start),
            cmp::min(self.end, other.end),
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

    /// Returns an iterator of at most two ranges encoding the set difference `self - other`. The
    /// iterator is guaranteed to be increasing according to `Range::partial_ord`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aocutil::range::Range;
    ///
    /// let mut diff = Range::new(0, 100).difference(25..=75);
    /// assert_eq!(diff.next(), Some(Range::new(0, 24)));
    /// assert_eq!(diff.next(), Some(Range::new(76, 100)));
    /// assert_eq!(diff.next(), None);
    ///
    /// let mut diff = Range::new(0, 100).difference(50..=150);
    /// assert_eq!(diff.next(), Some(Range::new(0, 49)));
    /// assert_eq!(diff.next(), None);
    ///
    /// let mut diff = Range::new(25, 50).difference(0..=100);
    /// assert_eq!(diff.next(), None);
    /// ```
    pub fn difference(self, other: impl Into<Range<T>>) -> impl DoubleEndedIterator<Item = Self>
    where
        T: DiscreteOrd,
    {
        let other: Range<T> = other.into();

        let intersect = self.intersects(&other);

        [
            Range::new(self.start, other.start.predecessor()),
            Range::new(other.end.successor(), self.end),
        ]
        .into_iter()
        .filter(move |r| intersect && !r.is_empty())
    }
}

#[test]
fn disjoint_difference() {
    let a = Range::new(50, 100);
    let b = Range::new(0, 0);

    let mut diff = a.difference(b);
    assert_eq!(diff.next(), None);

    let mut diff = b.difference(a);
    assert_eq!(diff.next(), None);
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
