use std::iter;

use crate::{
    geometry::{LineDirection, RookDirection, Vector},
    v,
};

use super::{AsBounds, DiscreteOrd, Range};

pub trait MultiAsBounds<T, const DIM: usize> {
    fn start_component(&self, dim: usize) -> &T;
    fn end_component(&self, dim: usize) -> &T;

    fn iter_start_components<'a>(&'a self) -> impl Iterator<Item = &'a T>
    where
        T: 'a,
    {
        (0..DIM).map(|dim| self.start_component(dim))
    }

    fn iter_end_components<'a>(&'a self) -> impl Iterator<Item = &'a T>
    where
        T: 'a,
    {
        (0..DIM).map(|dim| self.end_component(dim))
    }

    fn iter_components<'a>(&'a self) -> impl Iterator<Item = Range<&T>>
    where
        T: 'a,
    {
        iter::zip(self.iter_start_components(), self.iter_end_components())
            .map(|(a, b)| Range::new(a, b))
    }
}

impl<T, const DIM: usize> MultiAsBounds<T, DIM> for Vector<T, DIM> {
    fn start_component(&self, dim: usize) -> &T {
        &self.components[dim]
    }

    fn end_component(&self, dim: usize) -> &T {
        &self.components[dim]
    }
}

impl<T, const DIM: usize> MultiAsBounds<T, DIM> for MultiRange<T, DIM> {
    fn start_component(&self, dim: usize) -> &T {
        &self.components[dim].start
    }

    fn end_component(&self, dim: usize) -> &T {
        &self.components[dim].end
    }
}

/// An inclusive multidimensional range representing all values `x: Vector<T, DIM>` such that `x[n]`
/// is in `range.components[n]` for all `n` in `0..DIM`.
#[derive(Hash, Copy, Clone, PartialEq, Eq, Debug)]
pub struct MultiRange<T, const DIM: usize> {
    pub components: [Range<T>; DIM],
}

// impl<T, const DIM: usize> Debug for MultiRange<T, DIM> {}

impl<T, const DIM: usize> MultiRange<T, DIM> {
    pub const fn from_components(components: [Range<T>; DIM]) -> Self {
        Self { components }
    }

    pub fn from_corners(start: Vector<T, DIM>, end: Vector<T, DIM>) -> Self {
        Self {
            components: Vector::zip_with(start, end, |a, b| Range::new(a, b)).components,
        }
    }

    pub fn with_component(mut self, d: usize, new_component: Range<T>) -> Self {
        self.components[d] = new_component;
        self
    }

    pub fn is_empty(&self) -> bool
    where
        T: PartialOrd,
    {
        self.components.iter().all(Range::is_empty)
    }

    pub fn from_corners_ordered(start: Vector<T, DIM>, end: Vector<T, DIM>) -> Self
    where
        T: Ord,
    {
        Self {
            components: Vector::zip_with(start, end, |a, b| Range::ordered(a, b)).components,
        }
    }

    pub fn singleton(val: Vector<T, DIM>) -> Self
    where
        T: Clone,
    {
        Self {
            components: val.components.map(Range::singleton),
        }
    }

    /// Are all vectors in `other` also in `self`?
    pub fn contains(&self, other: &impl MultiAsBounds<T, DIM>) -> bool
    where
        T: PartialOrd,
    {
        iter::zip(&self.components, other.iter_components())
            .all(|(self_range, val_range)| self_range.contains(&val_range))
    }

    /// Does there exist a vector contained in both ranges?
    pub fn intersects(&self, other: &impl MultiAsBounds<T, DIM>) -> bool
    where
        T: PartialOrd,
    {
        iter::zip(&self.components, other.iter_components()).all(|(a, b)| a.intersects(&b))
    }

    /// Do the components of these ranges all touch axiswise?
    ///
    /// Equivalent condition: do there exist an `x` in `self` and `y` in `other` which are separated
    /// by at most a `QueenDirection`?
    pub fn touches_diagonally(&self, other: &impl MultiAsBounds<T, DIM>) -> bool
    where
        T: DiscreteOrd,
    {
        iter::zip(&self.components, other.iter_components()).all(|(a, b)| a.touches(&b))
    }

    /// Two `MultiRange`s *touch* iff their components all intersect axiswise, possibly except for
    /// on a single axis in which they may only touch.
    ///
    /// Equivalent condition: do there exist an `x` in `self` and `y` in `other` which are separated
    /// by at most a `RookDirection`?
    pub fn touches(&self, other: &impl MultiAsBounds<T, DIM>) -> bool
    where
        T: DiscreteOrd,
    {
        let mut found_touching_face = false;

        iter::zip(&self.components, other.iter_components()).all(|(a, b)| {
            if a.intersects(&b) {
                true
            } else if !found_touching_face && a.touches(&b) {
                found_touching_face = true;
                true
            } else {
                false
            }
        })
    }

    pub fn touching_face(&self, other: &impl MultiAsBounds<T, DIM>) -> Option<RookDirection<DIM>>
    where
        T: DiscreteOrd,
    {
        let mut touching_face = None;

        for (i, (a, b)) in iter::zip(&self.components, other.iter_components()).enumerate() {
            if a.intersects(&b) {
                continue;
            }

            if touching_face.is_none() && a.touches(&b) {
                let touching_direction = if &a.end < b.start {
                    LineDirection::Positive
                } else {
                    LineDirection::Negative
                };

                touching_face = Some(RookDirection::new(i, touching_direction));
            } else {
                return None;
            }
        }

        touching_face
    }

    pub fn touches_some_face(&self, other: &impl MultiAsBounds<T, DIM>) -> bool
    where
        T: DiscreteOrd,
    {
        self.touching_face(other).is_some()
    }

    pub fn touches_face(&self, face: RookDirection<DIM>, other: &impl MultiAsBounds<T, DIM>) -> bool
    where
        T: DiscreteOrd,
    {
        self.touching_face(other) == Some(face)
    }

    pub fn difference(mut self, other: impl Into<Self>) -> impl Iterator<Item = Self>
    where
        T: DiscreteOrd + Ord + Clone,
    {
        let other: Self = other.into();

        other
            .components
            .into_iter()
            .enumerate()
            .map(move |(i, other_component)| {
                let self0 = self.clone();

                let res = self.components[i]
                    .clone()
                    .difference(other_component.clone())
                    .map(move |c| self0.clone().with_component(i, c));

                self.components[i] = self.components[i].clone().intersection(other_component);

                res
            })
            .flatten()
    }
}

#[test]
fn test_difference() {
    let a = MultiRange::from_corners(v!(0, 0), v!(100, 100));

    let b = MultiRange::from_corners(v!(25, 25), v!(75, 75));
    itertools::assert_equal(
        a.difference(b),
        [
            MultiRange::from_corners(v!(0, 0), v!(24, 100)),
            MultiRange::from_corners(v!(76, 0), v!(100, 100)),
            MultiRange::from_corners(v!(25, 0), v!(75, 24)),
            MultiRange::from_corners(v!(25, 76), v!(75, 100)),
        ],
    );

    let c = MultiRange::singleton(v!(0, 0));
    itertools::assert_equal(
        a.difference(c),
        [
            MultiRange::from_corners(v!(1, 0), v!(100, 100)),
            MultiRange::from_corners(v!(0, 1), v!(0, 100)),
        ],
    );

    println!("1");
    itertools::assert_equal(b.difference(c), []);
    println!("2");
    itertools::assert_equal(c.difference(b), []);

    let d = MultiRange::singleton(v!(50, 0));
    println!("3");
    itertools::assert_equal(b.difference(d), []);
    println!("4");
    itertools::assert_equal(d.difference(b), []);
}

#[test]
fn test_contains() {
    let a = MultiRange::from_corners(v!(1, 1), v!(5, 5));
    let b = MultiRange::from_corners(v!(0, 2), v!(6, 4));

    assert!(!a.contains(&b));
    assert!(!b.contains(&a));

    let c = MultiRange::from_corners(v!(0, 0), v!(6, 6));
    let d = MultiRange::singleton(v!(3, 3));

    assert!(c.contains(&a));
    assert!(c.contains(&b));
    assert!(c.contains(&d));

    assert!(!a.contains(&c));
    assert!(!b.contains(&c));
    assert!(!d.contains(&c));

    assert!(a.contains(&d));
    assert!(b.contains(&d));

    assert!(a.contains(&a));
    assert!(b.contains(&b));
    assert!(c.contains(&c));
    assert!(d.contains(&d));
}

#[test]
fn test_intersects() {
    let a = MultiRange::from_corners(v!(0, 0), v!(12, 12));
    let b = MultiRange::from_corners(v!(6, 13), v!(18, 24));

    assert!(!a.intersects(&b));
    assert!(!b.intersects(&a));

    let c = MultiRange::from_corners_ordered(v!(13, 6), v!(24, 18));

    assert!(!a.intersects(&c));
    assert!(!c.intersects(&a));
    assert!(b.intersects(&c));
    assert!(c.intersects(&b));

    let d = MultiRange::singleton(v!(6, 6));

    assert!(a.intersects(&d));
    assert!(d.intersects(&a));

    assert!(!b.intersects(&d));
    assert!(!c.intersects(&d));
    assert!(!d.intersects(&b));
    assert!(!d.intersects(&c));

    assert!(a.intersects(&a));
    assert!(b.intersects(&b));
    assert!(c.intersects(&c));
    assert!(d.intersects(&d));
}
