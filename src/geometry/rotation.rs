use super::{RookDirection, Vector, BASIS_LETTERS};

use std::{fmt::Debug, iter};

/// # Panics
///
/// This function will panic if `permutation` is not a permutation of the array
/// `[0, 1, ..., DIM - 1]`.
pub fn permute<T, const DIM: usize>(arr: &mut [T; DIM], mut permutation: [usize; DIM]) {
    let mut i = 0;
    while i < DIM {
        while permutation[i] != i {
            let dst = permutation[i];
            arr.swap(i, dst);
            permutation.swap(i, dst);
        }
        i += 1;
    }
}

#[test]
fn test_permute() {
    let mut arr = ['a', 'b', 'c', 'd'];
    permute(&mut arr, [3, 2, 1, 0]);
    assert_eq!(arr, ['d', 'c', 'b', 'a']);

    permute(&mut arr, [0, 1, 3, 2]);
    assert_eq!(arr, ['d', 'c', 'a', 'b']);

    permute(&mut arr, [1, 2, 3, 0]);
    assert_eq!(arr, ['b', 'd', 'c', 'a']);

    permute(&mut arr, [1, 3, 2, 0]);
    assert_eq!(arr, ['a', 'b', 'c', 'd']);
}

/// Takes a permutation, expressed as an array of destinations, and returns whether the parity of
/// the permutation is even.
pub fn is_even_permutation<const DIM: usize>(mut permutation: [usize; DIM]) -> bool {
    let mut is_even = true;

    for i in 0..DIM {
        while permutation[i] != i {
            let dst = permutation[i];
            permutation.swap(i, dst);
            is_even = !is_even;
        }
    }

    is_even
}

#[test]
fn test_is_even_permutation() {
    assert!(is_even_permutation([3, 2, 1, 0]));
    assert!(!is_even_permutation([0, 1, 3, 2]));
    assert!(!is_even_permutation([1, 2, 3, 0]));
    assert!(is_even_permutation([1, 3, 2, 0]));
}

/// A rotation is a transformation of `Z^DIM` consisting of a permutation and negation of
/// coordinates which preserves orientation.
// you can think of this as a representation of a `DIM*DIM` rotation matrix, where `permutation[i]`
// tells you which position of the `i`th column is nonzero, and `negation[i]` tells you whether
// that is a `-1` instead of a `1`. to apply a rotation to a vector, first apply the negation,
// followed by the permutation.
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub struct Rotation<const DIM: usize> {
    permutation: [usize; DIM],
    negation: [bool; DIM],
}

impl<const DIM: usize> Debug for Rotation<DIM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut it = iter::zip(&self.permutation, &self.negation).peekable();
        write!(f, "[")?;
        while let Some((i, n)) = it.next() {
            write!(f, "{}{}", if *n { "-" } else { "" }, BASIS_LETTERS[*i])?;
            if it.peek().is_some() {
                write!(f, " ")?;
            }
        }
        write!(f, "]")?;

        Ok(())
    }
}

// #[test]
// fn test_debug() {
//     assert_eq!(
//         format!("{:?}", Rotation::<2>::from_quarter_turns(1)),
//         "[j -i]"
//     );
// }

impl<const DIM: usize> Rotation<DIM> {
    pub fn none() -> Self {
        let mut permutation = [0; DIM];
        for i in 0..DIM {
            permutation[i] = i;
        }

        Self {
            permutation,
            negation: [false; DIM],
        }
    }

    pub fn try_from_permutation_and_negation(
        permutation: [usize; DIM],
        negation: [bool; DIM],
    ) -> Option<Self> {
        let is_even_permutation = is_even_permutation(permutation);
        let is_even_negation = negation.iter().fold(true, |ev, n| ev ^ *n);

        if is_even_permutation ^ is_even_negation {
            return None;
        }

        Some(Self {
            permutation,
            negation,
        })
    }
}

// impl<T, const DIM: usize> Vector<T, DIM> {
//     pub fn rotated(mut self, rotation: Rotation<DIM>) -> Self {
//         for
//     }
// }

// impl Rotation<2> {
//     pub fn from_quarter_turns(quarter_turns: usize) -> Self {
//         let permutation = if quarter_turns % 2 == 0 {
//             [0, 1]
//         } else {
//             [1, 0]
//         };

//         let negation = [(quarter_turns % 4) > 1, (quarter_turns + 1) % 4 > 1];

//         Self {
//             permutation,
//             negation,
//         }
//     }
// }

// #[test]
// fn test_rotation_2_from_quarter_turns() {
//     let rot = Rotation::<2>::from_quarter_turns(0);
//     assert_eq!(
//         RookDirection::PLUS_X.unit_vector().rotated(rot),
//         RookDirection::PLUS_X.unit_vector(),
//     );

//     let rot = Rotation::<2>::from_quarter_turns(1);
//     assert_eq!(
//         RookDirection::PLUS_X.unit_vector().rotated(rot),
//         RookDirection::PLUS_Y.unit_vector(),
//     );

//     let rot = Rotation::<2>::from_quarter_turns(2);
//     assert_eq!(
//         RookDirection::PLUS_X.unit_vector().rotated(rot),
//         RookDirection::MINUS_X.unit_vector(),
//     );

//     let rot = Rotation::<2>::from_quarter_turns(3);
//     assert_eq!(
//         RookDirection::PLUS_X.unit_vector().rotated(rot),
//         RookDirection::MINUS_Y.unit_vector(),
//     );
// }
