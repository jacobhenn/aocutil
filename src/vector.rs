use crate::{array_zip_with, metric::Metric, ArrayCounter, Endianness, PlaneAxis};

use std::{
    array,
    fmt::{Debug, Display, Write},
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, Neg, Sub, SubAssign},
};

use num::{One, Zero};

#[macro_export]
macro_rules! v {
    ( $($idx:expr),* ) => { Vector::new([$($idx),*]) };
    ( $val:expr; $num:expr ) => { Vector::new([$val; $num]) };
}

/// NB: The `Ord` implementation for `Vector` is simply lexicographic. Only use it for stuff
/// like `BTreeSet` or `slice::binary_search`.
#[derive(PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
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

// TODO: make this general; return a `QueenDirection`
// impl<T> Vector<T, 2> {
//     /// Returns the quadrant this vector points to, or the cardinal direction if the vector is
//     /// strictly axis-aligned, or `None` if the vector is zero.
//     pub fn quadrant(self) -> Option<PrincipalWind>
//     where
//         T: Signed,
//     {
//         match (signum(&self[0]), signum(&self[1])) {
//             (Signum::Zero, Signum::Zero) => None,
//             (Signum::Plus, Signum::Zero) => Some(PrincipalWind::East),
//             (Signum::Plus, Signum::Plus) => Some(PrincipalWind::Northeast),
//             (Signum::Zero, Signum::Plus) => Some(PrincipalWind::North),
//             (Signum::Minus, Signum::Plus) => Some(PrincipalWind::Northwest),
//             (Signum::Minus, Signum::Zero) => Some(PrincipalWind::West),
//             (Signum::Minus, Signum::Minus) => Some(PrincipalWind::Southwest),
//             (Signum::Zero, Signum::Minus) => Some(PrincipalWind::South),
//             (Signum::Plus, Signum::Minus) => Some(PrincipalWind::Southeast),
//         }
//     }
// }

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
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('⟨')?;
        let mut components = self.components.iter().peekable();
        while let Some(component) = components.next() {
            if components.peek().is_some() {
                write!(f, "{}, ", component)?;
            } else {
                write!(f, "{}", component)?;
            }
        }
        f.write_char('⟩')?;
        Ok(())
    }
}

impl<T, const DIM: usize> Debug for Vector<T, DIM>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('⟨')?;
        let mut components = self.components.iter().peekable();
        while let Some(component) = components.next() {
            if components.peek().is_some() {
                write!(f, "{:?}, ", component)?;
            } else {
                write!(f, "{:?}", component)?;
            }
        }
        f.write_char('⟩')?;
        Ok(())
    }
}

#[test]
fn test_vector_display() {
    assert_eq!(v!(5, 7, 8).to_string(), "⟨5, 7, 8⟩");
}

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
}

impl<const DIM: usize> Debug for RookDirection<DIM> {
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

impl<T, const DIM: usize> From<RookDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero,
{
    fn from(value: RookDirection<DIM>) -> Self {
        let mut res = Vector::from_fn(|_| T::zero());
        res[value.axis] = match value.sign {
            LineDirection::Negative => T::one().neg(),
            LineDirection::Positive => T::one(),
        };
        res
    }
}

impl<T, const DIM: usize> Add<RookDirection<DIM>> for Vector<T, DIM>
where
    T: Neg<Output = T> + One + Zero + AddAssign,
{
    type Output = Self;

    fn add(mut self, rhs: RookDirection<DIM>) -> Self::Output {
        self.components[rhs.axis] += rhs.sign.to_num();
        self
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
fn direction_iter() {
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
        value.sign
    }
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

    pub fn perpendicular_axis(self) -> usize {
        (self.axis() + 1) % 2
    }

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

    // pub fn from_nesw(c: &str) -> Option<Self> {
    //     match c {
    //         "N" => Some(Self::NORTH),
    //         "E" => Some(Self::EAST),
    //         "S" => Some(Self::SOUTH),
    //         "W" => Some(Self::WEST),
    //         _ => None,
    //     }
    // }

    // pub fn from_wasd(c: &str) -> Option<Self> {
    //     match c {
    //         "W" => Some(Self::NORTH),
    //         "A" => Some(Self::WEST),
    //         "S" => Some(Self::SOUTH),
    //         "D" => Some(Self::EAST),
    //         _ => None,
    //     }
    // }
}

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct BishopDirection<const DIM: usize> {
    components: [LineDirection; DIM],
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
}

impl<T, const DIM: usize> From<BishopDirection<DIM>> for Vector<T, DIM>
where
    T: One + Neg<Output = T>,
{
    fn from(value: BishopDirection<DIM>) -> Self {
        Self {
            components: value.components.map(LineDirection::to_num),
        }
    }
}

impl<T, const DIM: usize> Add<BishopDirection<DIM>> for Vector<T, DIM>
where
    T: One + Neg<Output = T> + Add<T>,
{
    type Output = Vector<<T as Add<T>>::Output, DIM>;

    fn add(self, rhs: BishopDirection<DIM>) -> Self::Output {
        self + Self::from(rhs)
    }
}

#[test]
fn test_bishop_direction_iter() {
    for dir in BishopDirection::<2>::iter() {
        println!("{dir:?}");
    }

    itertools::assert_equal(
        BishopDirection::<2>::iter(),
        [
            BishopDirection::SOUTH_WEST,
            BishopDirection::SOUTH_EAST,
            BishopDirection::NORTH_WEST,
            BishopDirection::NORTH_EAST,
        ],
    );
}

impl BishopDirection<2> {
    pub const SOUTH_WEST: Self = Self::new([LineDirection::Negative, LineDirection::Negative]);
    pub const SOUTH_EAST: Self = Self::new([LineDirection::Positive, LineDirection::Negative]);
    pub const NORTH_WEST: Self = Self::new([LineDirection::Negative, LineDirection::Positive]);
    pub const NORTH_EAST: Self = Self::new([LineDirection::Positive, LineDirection::Positive]);
}

#[test]
fn bishop_direction_to_vector() {
    assert_eq!(
        Into::<Vector<i32>>::into(BishopDirection::<2>::NORTH_WEST),
        v!(-1, 1)
    );
}
