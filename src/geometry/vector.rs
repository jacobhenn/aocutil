use crate::array_zip_with;

use super::{metric::Metric, PlaneAxis};

use std::{
    array,
    fmt::{Debug, Display, Write},
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, Neg, Sub, SubAssign},
};

#[macro_export]
macro_rules! v {
    ( $($idx:expr),* ) => { Vector::new([$($idx),*]) };
    ( $val:expr; $num:expr ) => { Vector::new([$val; $num]) };
}

/// NB: The `Ord` implementation for `Vector` is simply lexicographic. Only use it for stuff
/// like `BTreeSet` or `slice::binary_search`.
#[derive(PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct Vector<T, const DIM: usize = 2> {
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

// impl<T> Vector<T, 2> {
// /// Returns the quadrant this vector points to, or the cardinal direction if the vector is
// /// strictly axis-aligned, or `None` if the vector is zero.
// TODO: make this general; return a `QueenDirection`
// pub fn quadrant(self) -> Option<PrincipalWind>
// where
//     T: Signed,
// {
//     match (signum(&self[0]), signum(&self[1])) {
//         (Signum::Zero, Signum::Zero) => None,
//         (Signum::Plus, Signum::Zero) => Some(PrincipalWind::East),
//         (Signum::Plus, Signum::Plus) => Some(PrincipalWind::Northeast),
//         (Signum::Zero, Signum::Plus) => Some(PrincipalWind::North),
//         (Signum::Minus, Signum::Plus) => Some(PrincipalWind::Northwest),
//         (Signum::Minus, Signum::Zero) => Some(PrincipalWind::West),
//         (Signum::Minus, Signum::Minus) => Some(PrincipalWind::Southwest),
//         (Signum::Zero, Signum::Minus) => Some(PrincipalWind::South),
//         (Signum::Plus, Signum::Minus) => Some(PrincipalWind::Southeast),
//     }
// }
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
