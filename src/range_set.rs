use crate::range::{AsBounds, DiscreteOrd, Range};

use std::{borrow::Borrow, cmp::Ordering, fmt::Debug};

/// A set of values of type `T`, compressed by the use of ranges.
///
/// # Examples
///
/// ```
/// use aocutil::prelude::*;
///
/// let mut nums: RangeSet<i32> = RangeSet::new();
/// nums.insert(-3..=45);
/// nums.insert(6..=10);
/// nums.insert(45..=78);
/// nums.insert(-8..=-5);
///
/// let ranges: Vec<Range<i32>> = nums.into_ranges().collect();
/// assert_eq!(ranges, &[Range::new(-8, -5), Range::new(-3, 78)]);
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct RangeSet<T> {
    ranges: Vec<Range<T>>,
}

impl<T> Debug for RangeSet<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.ranges.iter()).finish()
    }
}

impl<T> RangeSet<T> {
    /// Makes a new, empty `RangeSet`.
    pub fn new() -> Self {
        Self { ranges: Vec::new() }
    }

    /// Tests if the range set contains the given key value.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        Q: Borrow<T>,
        T: PartialOrd,
    {
        self.ranges
            .binary_search_by(|range| {
                if range.contains(key.borrow()) {
                    Ordering::Equal
                } else if key.borrow() < &range.start {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            })
            .is_ok()
    }

    pub fn intersects(&self, rhs: &impl AsBounds<T>) -> bool
    where
        T: PartialOrd,
    {
        self.ranges
            .binary_search_by(|range| {
                let res = if range.intersects(rhs) {
                    Ordering::Equal
                } else if &range.start < rhs.start() {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
                res
            })
            .is_ok()
    }

    fn find_touching_range(&self, rhs: &impl AsBounds<T>) -> Result<usize, usize>
    where
        T: DiscreteOrd,
    {
        self.ranges.binary_search_by(|range| {
            let res = if range.touches(rhs) {
                Ordering::Equal
            } else if &range.start < rhs.start() {
                Ordering::Less
            } else {
                Ordering::Greater
            };
            res
        })
    }

    /// Tests if the set contains a range which intersects, or just touches, `val`.
    pub fn touches(&self, val: &impl AsBounds<T>) -> bool
    where
        T: DiscreteOrd,
    {
        self.find_touching_range(val).is_ok()
    }

    /// Inserts the given range into the set, merging with existing ranges if possible.
    pub fn insert(&mut self, new_range: impl Into<Range<T>>)
    where
        T: DiscreteOrd + Ord,
        Range<T>: Clone,
    {
        let mut new_range = new_range.into();

        match self.find_touching_range(&new_range) {
            Ok(center) => {
                new_range = new_range.hull(self.ranges[center].clone());

                let mut right_bound = self.ranges.len();
                if let Some(slice) = self.ranges.get((center + 1)..) {
                    for (i, range) in slice.iter().enumerate() {
                        if range.touches(&new_range) {
                            new_range = new_range.hull(range.clone());
                        } else {
                            right_bound = center + 1 + i;
                            break;
                        }
                    }
                }

                let mut left_bound = 0;
                if center != 0 {
                    for (i, range) in self.ranges[..=(center - 1)].iter().enumerate().rev() {
                        if range.touches(&new_range) {
                            new_range = new_range.hull(range.clone());
                        } else {
                            left_bound = i + 1;
                            break;
                        }
                    }
                }

                self.ranges[left_bound] = new_range;
                self.ranges.drain((left_bound + 1)..right_bound);
            }
            Err(i) => {
                self.ranges.insert(i, new_range);
            }
        }
    }

    /// Returns an iterator over references to the ranges of items this set conatins in sorted
    /// order.
    pub fn ranges(&self) -> impl Iterator<Item = &Range<T>> {
        self.ranges.iter()
    }

    /// Returns an iterator over the ranges of items this set conatins in sorted order.
    pub fn into_ranges(self) -> impl Iterator<Item = Range<T>> {
        self.ranges.into_iter()
    }

    /// Returns the maximum value contained in this set, or `None` if the set is empty.
    pub fn max(&self) -> Option<&T> {
        self.ranges.last().map(|r| &r.end)
    }

    /// Returns the minimum value contained in this set, or `None` if the set is empty.
    pub fn min(&self) -> Option<&T> {
        self.ranges.first().map(|r| &r.start)
    }
}

impl<T, S> FromIterator<S> for RangeSet<T>
where
    T: DiscreteOrd + Ord,
    Range<T>: From<S> + Clone,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = S>,
    {
        let mut res = Self::new();
        for item in iter {
            res.insert(Range::from(item));
        }
        res
    }
}

#[macro_export]
macro_rules! range_set {
    [ $($elem:expr),* ] => {
        {
            let mut res = RangeSet::new();
            $(
                res.insert($elem);
            )*
            res
        }
    }
}

#[test]
fn lots_of_merging() {
    let mut set = RangeSet::new();
    set.insert(1);
    set.insert(3);
    set.insert(5);
    set.insert(7);
    set.insert(9);
    set.insert(11);
    set.insert(13);

    set.insert(2..=11);

    assert_eq!(
        set.into_ranges().collect::<Vec<_>>(),
        &[Range::new(1, 11), Range::singleton(13)]
    );
}

#[test]
fn range_set_macro() {
    let mut set_a: RangeSet<i32> = RangeSet::new();
    set_a.insert(1..=5);
    set_a.insert(3..=8);
    set_a.insert(-4);
    set_a.insert(-8..=-6);

    let set_b = range_set![1..=5, 3..=8, -4, -8..=-6];

    assert_eq!(set_a, set_b);
}

#[test]
fn contains() {
    let set = range_set![0, 2];
    assert!(set.contains(&0));
    assert!(set.contains(&2));
    assert!(!set.contains(&1));
}

#[test]
fn intersects() {
    let set = range_set![0, 2..=9, 12..=17, 19..=20, 25, 27, 29..=37, 39];
    assert!(set.intersects(&Range::new(38, 41)));
}
