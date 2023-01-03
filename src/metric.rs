use crate::vector::Vector;

#[cfg(test)]
use crate::v;

use std::{iter::Sum, ops::Mul};

use num::{Signed, ToPrimitive};

pub trait Metric<T> {
    type Output;

    fn magnitude<const DIM: usize>(vec: Vector<T, DIM>) -> Self::Output;
}

pub struct Manhattan;

impl<T> Metric<T> for Manhattan
where
    T: Sum + Signed,
{
    type Output = T;

    fn magnitude<const DIM: usize>(vec: Vector<T, DIM>) -> Self::Output {
        vec.components.into_iter().map(|c| c.abs()).sum()
    }
}

pub struct SquaredEuclidean;

impl<T, O> Metric<T> for SquaredEuclidean
where
    T: Mul<Output = O> + Clone,
    O: Sum,
{
    type Output = O;

    fn magnitude<const DIM: usize>(vec: Vector<T, DIM>) -> Self::Output {
        vec.components.into_iter().map(|x| x.clone() * x).sum()
    }
}

pub struct Euclidean;

impl<T, O> Metric<T> for Euclidean
where
    T: Mul<Output = O> + Clone,
    O: Sum + ToPrimitive,
{
    type Output = f64;

    fn magnitude<const DIM: usize>(vec: Vector<T, DIM>) -> Self::Output {
        vec.magnitude::<SquaredEuclidean>()
            .to_f64()
            .expect("values in vector should be convertible to f64")
            .sqrt()
    }
}

pub struct Chessboard;

impl<T> Metric<T> for Chessboard
where
    T: Ord + Signed,
{
    type Output = T;

    fn magnitude<const DIM: usize>(vec: Vector<T, DIM>) -> Self::Output {
        vec.components
            .into_iter()
            .map(|c| c.abs())
            .max()
            .expect("tried to take chessboard magnitude of length-0 vector")
    }
}

#[test]
fn test_manhattan_magnitude() {
    assert_eq!(v!(1, 2, 3).magnitude::<Manhattan>(), 6);
    assert_eq!(v!(-1, -2, -3).magnitude::<Manhattan>(), 6);
}

#[test]
fn test_squared_euclidean_magnitude() {
    assert_eq!(v!(1, 2, 3).magnitude::<SquaredEuclidean>(), 14);
    assert_eq!(v!(-1, -2, -3).magnitude::<SquaredEuclidean>(), 14);
}

#[test]
fn test_euclidean_magnitude() {
    assert_eq!(v!(1, 2, 3).magnitude::<Euclidean>(), 14.0f64.powf(0.5));
    assert_eq!(v!(-1, -2, -3).magnitude::<Euclidean>(), 14.0f64.powf(0.5));
}

#[test]
fn test_chessboard_magnitude() {
    assert_eq!(v!(1, 2, 3).magnitude::<Chessboard>(), 3);
    assert_eq!(v!(-1, -2, -3).magnitude::<Chessboard>(), 3);
}

#[test]
fn test_chessboard_distance() {
    assert_eq!(v!(2, 4).distance::<Chessboard, _, _>(v!(4, 3)), 2);
    assert_eq!(v!(-2, -4).distance::<Chessboard, _, _>(v!(-4, -3)), 2);
}
