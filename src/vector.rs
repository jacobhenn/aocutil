use crate::{array_zip_with, metric::Metric, signum, PlaneAxis, Signum};

use std::{
    array,
    fmt::{Debug, Display, Write},
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, Neg, Sub, SubAssign},
};

use num::{One, Signed, Zero};

#[macro_export]
macro_rules! v {
    ( $($idx:expr),* ) => { Vector::new([$($idx),*]) };
    ( $val:expr; $num:expr ) => { Vector::new([$val; $num]) };
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct Vector<T = i32, const DIM: usize = 2> {
    pub components: [T; DIM],
}

impl<T, const DIM: usize> Vector<T, DIM> {
    pub fn new(components: [T; DIM]) -> Self {
        Self { components }
    }

    pub fn map<O>(self, f: impl Fn(T) -> O) -> Vector<O, DIM> {
        Vector {
            components: self.components.map(f),
        }
    }

    pub fn from_fn(f: impl FnMut(usize) -> T) -> Self {
        Self {
            components: array::from_fn(f),
        }
    }

    pub fn zip_with<U, O>(self, other: Vector<U, DIM>, f: impl Fn(T, U) -> O) -> Vector<O, DIM> {
        Vector {
            components: array_zip_with(self.components, other.components, f),
        }
    }

    pub fn magnitude<M: Metric<T>>(self) -> M::Output {
        M::magnitude(self)
    }

    pub fn distance<M: Metric<O>, U, O>(self, other: Vector<U, DIM>) -> M::Output
    where
        T: Sub<U, Output = O>,
    {
        M::magnitude(self - other)
    }

    pub fn with_component(mut self, idx: usize, val: T) -> Self {
        self[idx] = val;
        self
    }
}

impl<T> Vector<T, 2> {
    /// Returns the quadrant this vector points to, or the cardinal direction if the vector is
    /// strictly axis-aligned, or `None` if the vector is zero.
    pub fn quadrant(self) -> Option<PrincipalWind>
    where
        T: Signed,
    {
        match (signum(&self[0]), signum(&self[1])) {
            (Signum::Zero, Signum::Zero) => None,
            (Signum::Plus, Signum::Zero) => Some(PrincipalWind::East),
            (Signum::Plus, Signum::Plus) => Some(PrincipalWind::Northeast),
            (Signum::Zero, Signum::Plus) => Some(PrincipalWind::North),
            (Signum::Minus, Signum::Plus) => Some(PrincipalWind::Northwest),
            (Signum::Minus, Signum::Zero) => Some(PrincipalWind::West),
            (Signum::Minus, Signum::Minus) => Some(PrincipalWind::Southwest),
            (Signum::Zero, Signum::Minus) => Some(PrincipalWind::South),
            (Signum::Plus, Signum::Minus) => Some(PrincipalWind::Southeast),
        }
    }
}

// TODO: make this work for more tuples
impl<T> From<(T, T)> for Vector<T, 2> {
    fn from((a, b): (T, T)) -> Self {
        v!(a, b)
    }
}

impl<T> From<(T, T, T)> for Vector<T, 3> {
    fn from((a, b, c): (T, T, T)) -> Self {
        v!(a, b, c)
    }
}

impl<T, const DIM: usize> Index<usize> for Vector<T, DIM> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.components[index]
    }
}

impl<T, const DIM: usize> IndexMut<usize> for Vector<T, DIM> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.components[index]
    }
}

impl<T> Index<PlaneAxis> for Vector<T, 2> {
    type Output = T;

    fn index(&self, index: PlaneAxis) -> &Self::Output {
        &self.components[index as usize]
    }
}

impl<T> IndexMut<PlaneAxis> for Vector<T, 2> {
    fn index_mut(&mut self, index: PlaneAxis) -> &mut Self::Output {
        &mut self.components[index as usize]
    }
}

impl<T, U, const DIM: usize> Add<Vector<U, DIM>> for Vector<T, DIM>
where
    T: Add<U>,
{
    type Output = Vector<<T as Add<U>>::Output, DIM>;

    fn add(self, rhs: Vector<U, DIM>) -> Self::Output {
        self.zip_with(rhs, |t, u| t + u)
    }
}

impl<T, U, const DIM: usize> Sub<Vector<U, DIM>> for Vector<T, DIM>
where
    T: Sub<U>,
{
    type Output = Vector<<T as Sub<U>>::Output, DIM>;

    fn sub(self, rhs: Vector<U, DIM>) -> Self::Output {
        self.zip_with(rhs, |t, u| t - u)
    }
}

impl<T, const DIM: usize> Neg for Vector<T, DIM>
where
    T: Neg,
{
    type Output = Vector<<T as Neg>::Output, DIM>;

    fn neg(self) -> Self::Output {
        self.map(T::neg)
    }
}

impl<T, U, const DIM: usize> AddAssign<Vector<U, DIM>> for Vector<T, DIM>
where
    T: AddAssign<U>,
{
    fn add_assign(&mut self, rhs: Vector<U, DIM>) {
        for (self_component, rhs_component) in iter::zip(&mut self.components, rhs.components) {
            *self_component += rhs_component;
        }
    }
}

impl<T, U, const DIM: usize> SubAssign<Vector<U, DIM>> for Vector<T, DIM>
where
    T: SubAssign<U>,
{
    fn sub_assign(&mut self, rhs: Vector<U, DIM>) {
        for (self_component, rhs_component) in iter::zip(&mut self.components, rhs.components) {
            *self_component -= rhs_component;
        }
    }
}

impl<T, U, const DIM: usize> Mul<T> for Vector<U, DIM>
where
    U: Mul<T>,
    T: Clone,
{
    type Output = Vector<<U as Mul<T>>::Output, DIM>;

    fn mul(self, rhs: T) -> Self::Output {
        self.map(|c| c * rhs.clone())
    }
}

impl<T, const DIM: usize> Display for Vector<T, DIM>
where
    T: Display + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "⟨{}⟩",
            self.components
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[test]
fn test_vector_display() {
    assert_eq!(v!(5, 7, 8).to_string(), "⟨5, 7, 8⟩");
}

/// A "cardinal direction" in `DIM`-dimensional space.
///
/// This is implemented by simply storing a number which indexes into the possible directions. It
/// is a logic error for the inner number to be `>= DIM`. If a `Direction` observes such an
/// error, its behavior is unspecified.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Direction<const DIM: usize> {
    axis: usize,
    sign: LineDirection,
}

impl<const DIM: usize> Direction<DIM> {
    pub fn new(axis: usize, sign: LineDirection) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self {
            axis,
            sign,
        }
    }

    pub fn negative(axis: usize) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self {
            axis,
            sign: LineDirection::Negative,
        }
    }

    pub fn positive(axis: usize) -> Self {
        assert!(axis < DIM, "axis out of range");
        Self {
            axis,
            sign: LineDirection::Positive,
        }
    }

    pub fn axis(self) -> usize {
        self.axis
    }

    pub fn sign(self) -> LineDirection {
        self.sign
    }

    pub fn iter() -> DirectionIter<DIM> {
        DirectionIter(Self {
            axis: 0,
            sign: LineDirection::Negative,
        })
    }
}

impl<const DIM: usize> Debug for Direction<DIM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.sign == LineDirection::Negative {
            f.write_char('-')?;
        } else {
            f.write_char('+')?;
        }

        if DIM < 5 {
            f.write_char(['x', 'y', 'z', 'w'][self.axis])
        } else {
            write!(f, "{}", self.axis)
        }
    }
}

impl<T, const DIM: usize> From<Direction<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero,
{
    fn from(value: Direction<DIM>) -> Self {
        let mut res = Vector::from_fn(|_| T::zero());
        res[value.axis] = match value.sign {
            LineDirection::Negative => T::one().neg(),
            LineDirection::Positive => T::one(),
        };
        res
    }
}

impl<T, const DIM: usize> Add<Direction<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero + AddAssign,
{
    type Output = Self;

    fn add(mut self, rhs: Direction<DIM>) -> Self::Output {
        self.components[rhs.axis] += rhs.sign.to_num();
        self
    }
}

impl<const DIM: usize> Neg for Direction<DIM> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            sign: -self.sign,
            ..self
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DirectionIter<const DIM: usize>(Direction<DIM>);

impl<const DIM: usize> Iterator for DirectionIter<DIM> {
    type Item = Direction<DIM>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.axis >= DIM {
            return None;
        }

        let res = self.0;
        self.0.sign = -self.0.sign;
        if self.0.sign == LineDirection::Negative {
            self.0.axis += 1;
        }

        Some(res)
    }
}

#[test]
fn direction_iter() {
    itertools::assert_equal(
        Direction::<2>::iter().map(|d| CardinalDirection::from(d)),
        [
            CardinalDirection::West,
            CardinalDirection::East,
            CardinalDirection::South,
            CardinalDirection::North,
        ],
    );
}

#[test]
fn unit_vector() {
    itertools::assert_equal(
        Direction::<2>::iter().map(|d| Vector::from(d)),
        [v!(-1, 0), v!(1, 0), v!(0, -1), v!(0, 1)],
    );
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum LineDirection {
    Negative,
    Positive,
}

impl LineDirection {
    pub fn to_num<T>(self) -> T
    where
        T: Zero + One + Neg<Output = T>,
    {
        match self {
            LineDirection::Negative => -T::one(),
            LineDirection::Positive => T::one(),
        }
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

impl From<Direction<1>> for LineDirection {
    fn from(value: Direction<1>) -> Self {
        value.sign
    }
}

impl Direction<1> {
    pub const NEGATIVE: Self = Self {
        axis: 0,
        sign: LineDirection::Negative,
    };

    pub const POSITIVE: Self = Self {
        axis: 0,
        sign: LineDirection::Positive,
    };
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum CardinalDirection {
    East,
    North,
    West,
    South,
}

impl From<Direction<2>> for CardinalDirection {
    fn from(value: Direction<2>) -> Self {
        if value.axis == 0 {
            match value.sign {
                LineDirection::Negative => Self::West,
                LineDirection::Positive => Self::East,
            }
        } else {
            match value.sign {
                LineDirection::Negative => Self::South,
                LineDirection::Positive => Self::North,
            }
        }
    }
}

impl Direction<2> {
    pub const EAST: Self = Self {
        axis: 0,
        sign: LineDirection::Positive,
    };

    pub const NORTH: Self = Self {
        axis: 1,
        sign: LineDirection::Positive,
    };

    pub const WEST: Self = Self {
        axis: 0,
        sign: LineDirection::Negative,
    };

    pub const SOUTH: Self = Self {
        axis: 1,
        sign: LineDirection::Negative,
    };

    pub fn from_udlr(c: &str) -> Option<Self> {
        match c {
            "U" => Some(Self::NORTH),
            "D" => Some(Self::SOUTH),
            "L" => Some(Self::WEST),
            "R" => Some(Self::EAST),
            _ => None,
        }
    }

    pub fn from_nesw(c: &str) -> Option<Self> {
        match c {
            "N" => Some(Self::NORTH),
            "E" => Some(Self::EAST),
            "S" => Some(Self::SOUTH),
            "W" => Some(Self::WEST),
            _ => None,
        }
    }

    pub fn from_wasd(c: &str) -> Option<Self> {
        match c {
            "W" => Some(Self::NORTH),
            "A" => Some(Self::WEST),
            "S" => Some(Self::SOUTH),
            "D" => Some(Self::EAST),
            _ => None,
        }
    }
}

/// A cardinal or intercardinal direction.
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum PrincipalWind {
    East,
    Northeast,
    North,
    Northwest,
    West,
    Southwest,
    South,
    Southeast,
}

impl From<PrincipalWind> for Vector {
    fn from(direction: PrincipalWind) -> Self {
        match direction {
            PrincipalWind::East => v!(1, 0),
            PrincipalWind::Northeast => v!(1, 1),
            PrincipalWind::North => v!(0, 1),
            PrincipalWind::Northwest => v!(-1, 1),
            PrincipalWind::West => v!(-1, 0),
            PrincipalWind::Southwest => v!(-1, -1),
            PrincipalWind::South => v!(0, -1),
            PrincipalWind::Southeast => v!(1, -1),
        }
    }
}
