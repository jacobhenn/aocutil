use std::{
    array,
    collections::{hash_map::DefaultHasher, HashMap},
    env,
    fmt::{self, Display},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
    ops::RangeInclusive,
    ptr,
    str::FromStr,
};

use itertools::Itertools;

use num::Signed;

pub mod geometry;

pub mod grid;

pub mod parse;

pub mod graph;

pub mod range;

pub mod range_set;

pub mod log;

pub mod radix;

pub mod prelude {
    pub use super::{
        geometry::*,
        graph::*,
        grid::*,
        parse::*,
        part::{self, AocPart, Part},
        radix::*,
        range::*,
        range_set::*,
        *,
    };

    pub use std::{
        any, array,
        cell::{self, Cell, RefCell},
        cmp::{self, Ordering},
        collections::*,
        env, f64, fmt,
        fmt::{Debug, Display, Write},
        fs,
        hash::{self, Hash, Hasher},
        hint, iter,
        marker::PhantomData,
        mem, ops, ptr,
        rc::{self, Rc},
        str::FromStr,
        sync::{self, RwLock},
        thread,
    };

    pub use tracing::*;

    pub use tracing_subscriber::util::SubscriberInitExt;

    pub use itertools::{self, Itertools};

    pub use anyhow::{anyhow, bail, Context};
}

#[derive(Debug, Copy, Clone)]
pub enum Endianness {
    /// The first element of the array is the most significant
    Big,
    /// The first element of the array is the least significant
    Little,
}

pub struct ArrayCounter<const LEN: usize> {
    endianness: Endianness,
    base: usize,
    done: bool,
    current: [usize; LEN],
}

impl<const LEN: usize> ArrayCounter<LEN> {
    pub fn new(endianness: Endianness, base: usize) -> Self {
        Self {
            endianness,
            base,
            done: false,
            current: [0; LEN],
        }
    }

    pub fn starting_at(endianness: Endianness, base: usize, current: [usize; LEN]) -> Self {
        Self {
            endianness,
            base,
            done: false,
            current,
        }
    }
}

impl<const LEN: usize> Iterator for ArrayCounter<LEN> {
    type Item = [usize; LEN];

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let next_i = |i| match self.endianness {
            Endianness::Big => i - 1,
            Endianness::Little => i + 1,
        };

        let most_significant_i = match self.endianness {
            Endianness::Big => 0,
            Endianness::Little => LEN - 1,
        };

        let res = self.current;

        let mut i = match self.endianness {
            Endianness::Big => LEN - 1,
            Endianness::Little => 0,
        };

        let mut carry = true;
        while carry {
            if self.current[i] == self.base - 1 {
                self.current[i] = 0;

                if i == most_significant_i {
                    self.done = true;
                    break;
                } else {
                    i = next_i(i);
                }
            } else {
                self.current[i] += 1;
                carry = false;
            }
        }

        Some(res)
    }
}

#[test]
fn test_array_counter() {
    let mut counter = ArrayCounter::<3>::new(Endianness::Little, 3);
    assert_eq!(counter.nth(5), Some([2, 1, 0]));
    assert_eq!(counter.nth(20), Some([2, 2, 2]));

    let mut counter = ArrayCounter::<3>::new(Endianness::Big, 3);
    assert_eq!(counter.nth(5), Some([0, 1, 2]));
}

pub const DIGIT_NAMES: [&str; 10] = [
    "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
];

pub enum Signum {
    Minus,
    Zero,
    Plus,
}

pub fn signum(x: &impl Signed) -> Signum {
    if x.is_negative() {
        Signum::Minus
    } else if x.is_positive() {
        Signum::Plus
    } else {
        Signum::Zero
    }
}

pub fn hash(x: impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    x.hash(&mut hasher);
    hasher.finish()
}

pub trait IsSigned {
    const IS_SIGNED: bool;
}

macro_rules! impl_is_signed {
    { signed: $($st:ty)*; unsigned: $($ut:ty)* } => {
        $(
            impl IsSigned for $st {
                const IS_SIGNED: bool = true;
            }
        )*

        $(
            impl IsSigned for $ut {
                const IS_SIGNED: bool = false;
            }
        )*
    }
}

impl_is_signed! { signed: i8 i16 i32 i64 i128 isize; unsigned: u8 u16 u32 u64 u128 usize }

pub struct IntsRanges<'a, T> {
    src: &'a str,
    _marker: PhantomData<T>,
}

impl<'a, T> Iterator for IntsRanges<'a, T>
where
    T: FromStr + IsSigned,
{
    type Item = (RangeInclusive<usize>, T);

    fn next(&mut self) -> Option<Self::Item> {
        let next_num_start = self
            .src
            .find(|c: char| c.is_ascii_digit() || (T::IS_SIGNED && c == '-'))?;
        self.src = &self.src[next_num_start..];
        if let Some(next_num_end) = self.src[1..].find(|c: char| !c.is_ascii_digit()) {
            let Ok(res) = self.src[..=next_num_end].parse::<T>() else {
                return self.next();
            };
            self.src = &self.src[(next_num_end + 1)..];
            Some((next_num_start..=next_num_end, res))
        } else {
            let Ok(res) = self.src.parse::<T>() else {
                return self.next();
            };
            let range = next_num_start..=(self.src.len() - 1);
            self.src = "";
            Some((range, res))
        }
    }
}

pub struct Ints<'a, T> {
    ints_ranges: IntsRanges<'a, T>,
}

impl<'a, T> Iterator for Ints<'a, T>
where
    T: FromStr + IsSigned,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.ints_ranges.next().map(|(_, n)| n)
    }
}

pub fn ints<T>(src: &str) -> Ints<T> {
    Ints {
        ints_ranges: intsranges(src),
    }
}

pub fn intsranges<T>(src: &str) -> IntsRanges<T> {
    IntsRanges {
        src,
        _marker: PhantomData::<T>,
    }
}

#[test]
fn test_ints() {
    let src = "456-784.||&45                   789     48";
    let mut ints = ints::<i32>(src);
    assert_eq!(ints.next(), Some(456));
    assert_eq!(ints.next(), Some(-784));
    assert_eq!(ints.next(), Some(45));
    assert_eq!(ints.next(), Some(789));
    assert_eq!(ints.next(), Some(48));
    assert_eq!(ints.next(), None);
}

#[test]
fn test_uints() {
    let src = "456-784.||&45                   --789     48";
    let mut ints = ints::<u32>(src);
    assert_eq!(ints.next(), Some(456));
    assert_eq!(ints.next(), Some(784));
    assert_eq!(ints.next(), Some(45));
    assert_eq!(ints.next(), Some(789));
    assert_eq!(ints.next(), Some(48));
    assert_eq!(ints.next(), None);
}

pub fn int(src: &str) -> i32 {
    src.parse::<i32>().unwrap()
}

#[derive(Debug, Clone, Copy)]
pub struct ArrayChunks<T, const N: usize> {
    inner: T,
}

impl<T, const N: usize> Iterator for ArrayChunks<T, N>
where
    T: Iterator,
{
    type Item = [T::Item; N];

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.fill_array()
    }
}

pub trait IteratorExt: Iterator + Sized {
    fn vec(self) -> Vec<Self::Item> {
        self.collect()
    }

    fn log_dbg(self) -> Self
    where
        Self: Clone,
        Self::Item: fmt::Debug,
    {
        tracing::debug!("{:?}", self.clone().collect_vec());
        self
    }

    fn fill_array<const N: usize>(&mut self) -> Option<[Self::Item; N]> {
        let mut res =
            unsafe { MaybeUninit::<[MaybeUninit<Self::Item>; N]>::uninit().assume_init() };

        for slot in &mut res {
            slot.write(self.next()?);
        }

        Some(res.map(|u| unsafe { u.assume_init() }))
    }

    fn util_array_chunks<const N: usize>(self) -> ArrayChunks<Self, N> {
        ArrayChunks { inner: self }
    }

    fn hash(self) -> u64
    where
        Self::Item: Hash,
    {
        let mut hasher = DefaultHasher::new();
        for item in self {
            item.hash(&mut hasher);
        }
        hasher.finish()
    }
}

impl<T> IteratorExt for T where T: Iterator {}

#[test]
fn test_fill_array() {
    let mut it = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].into_iter();

    assert_eq!(it.fill_array::<3>(), Some([0, 1, 2]));
    assert_eq!(it.fill_array::<0>(), Some([]));
    assert_eq!(it.fill_array::<3>(), Some([3, 4, 5]));
    assert_eq!(it.fill_array::<10>(), None);
}

pub fn transpose<T>(vecs: Vec<Vec<T>>) -> Vec<Vec<T>>
where
    T: Clone,
{
    let mut out = Vec::new();
    let Some(max_len) = vecs.iter().map(Vec::len).max() else {
        return out;
    };
    for i in 0..max_len {
        let mut col = Vec::new();
        for vec in &vecs {
            let Some(i) = vec.get(i) else {
                continue;
            };
            col.push(i.clone());
        }
        out.push(col);
    }
    out
}

#[test]
fn test_transpose() {
    let v = vec![
        vec![1, 2, 3, 4, 5],
        vec![1, 2, 3, 4, 5],
        vec![1, 2, 5, 4, 5],
        vec![1, 2, 3, 4, 5],
        vec![1, 2, 5, 4, 5],
        vec![1, 2, 3, 4, 5],
    ];
    assert_eq!(
        transpose(v),
        vec![
            vec![1, 1, 1, 1, 1, 1],
            vec![2, 2, 2, 2, 2, 2],
            vec![3, 3, 5, 3, 5, 3],
            vec![4, 4, 4, 4, 4, 4],
            vec![5, 5, 5, 5, 5, 5],
        ]
    );
}

pub fn counts<T: Eq + Hash, I: IntoIterator<Item = T>>(iter: I) -> HashMap<T, usize> {
    let mut res = HashMap::new();
    for item in iter {
        *res.entry(item).or_insert(0) += 1;
    }
    res
}

pub fn array_zip_with<const N: usize, L, R, O>(
    lhs: [L; N],
    rhs: [R; N],
    f: impl Fn(L, R) -> O,
) -> [O; N] {
    array::from_fn(|i| unsafe { f(ptr::read(&lhs[i]), ptr::read(&rhs[i])) })
}

#[test]
fn test_counts() {
    let v = vec!['a', 'b', 'a', 'c', 'b', 'f', 'a'];
    let counts = counts(v);
    assert_eq!(counts[&'a'], 3);
    assert_eq!(counts[&'b'], 2);
    assert_eq!(counts[&'c'], 1);
}

pub fn factor(mut n: u32) -> HashMap<u32, usize> {
    const WHEEL_BASIS: &[u32] = &[2, 3, 5];

    const WHEEL_DELTAS: &[u32] = &[4, 2, 4, 2, 4, 6, 2, 6];

    let mut factors = HashMap::new();
    for divisor in WHEEL_BASIS {
        while n % divisor == 0 {
            *factors.entry(*divisor).or_insert(0) += 1;
            n /= divisor;
        }
    }

    let mut divisor = 7;
    for delta in WHEEL_DELTAS.iter().cycle() {
        if divisor * divisor > n {
            break;
        }

        while n % divisor == 0 {
            *factors.entry(divisor).or_insert(0) += 1;
            n /= divisor;
        }

        divisor += delta;
    }

    if n > 1 {
        *factors.entry(n).or_insert(0) += 1;
    }

    factors
}

pub mod part {
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub enum Part {
        One,
        Two,
    }

    pub trait AocPart {
        const PART: Part;

        fn part() -> Part {
            Self::PART
        }

        fn is_one() -> bool {
            matches!(Self::PART, Part::One)
        }

        fn is_two() -> bool {
            matches!(Self::PART, Part::Two)
        }
    }

    pub struct One;

    impl AocPart for One {
        const PART: Part = Part::One;
    }

    pub struct Two;

    impl AocPart for Two {
        const PART: Part = Part::Two;
    }

    // i know this is stupid but i somehow messed it up before so the test stays
    #[test]
    fn test_parts() {
        fn assert_is_part_one<Part: AocPart>() {
            assert!(Part::is_one());
            assert!(!Part::is_two());
        }

        fn assert_is_part_two<Part: AocPart>() {
            assert!(Part::is_two());
            assert!(!Part::is_one());
        }

        assert_is_part_one::<One>();
        assert_is_part_two::<Two>();
    }
}

pub fn get_input(year: usize, day: usize) -> String {
    std::fs::read_to_string(format!(
        "{}/{year}/{day}",
        env::var("AOC_INPUT_DIR").expect("environment variable AOC_INPUT_DIR should be set")
    ))
    .expect("input file should be present")
}

/// this is semi-deprecated
#[macro_export]
macro_rules! example_tests {
    {
        - part one:
            $($p1n:ident: $p1in:expr => $p1out:expr,)*
        - part two:
            $($p2n:ident: $p2in:expr => $p2out:expr,)*
    } => {
        $(
            #[test]
            #[allow(unreachable_code)]
            fn $p1n() {
                let _ = aocutil::log::test_subscriber().try_init();
                assert_eq!(solve::<aocutil::part::One>($p1in), $p1out);
            }
        )*

        $(
            #[test]
            #[allow(unreachable_code)]
            fn $p2n() {
                let _ = aocutil::log::test_subscriber().try_init();
                assert_eq!(solve::<aocutil::part::Two>($p2in), $p2out);
            }
        )*
    }
}

#[macro_export]
macro_rules! aoc_test {
    (
        $name:ident: $part:path, $(@$input:ident)? $($in:expr),* => $out:expr
    ) => {
        #[test]
        #[allow(unreachable_code)]
        fn $name() {
            let _ = aocutil::log::test_subscriber().try_init();
            assert_eq!(
                solve::<$part>(
                    $({
                        stringify!($input);
                        &aocutil::get_input(YEAR, DAY)
                    },)?
                    $($in),*
                ),
                $out,
            );
        }
    };
}

#[macro_export]
macro_rules! aoc_tests {
    {
        inputs {
            $(
                $in_name:ident = $in_val:expr,
            )*
        }

        $(
            $part:path {
                $(
                    $name:ident: $(@$input:ident)? $($in:expr),* => $out:expr,
                )*
            }
        )*
    } => {
        $(
            #[allow(non_upper_case_globals)]
            const $in_name: &str = $in_val;
        )*

        $(
            $(
                aoc_test!($name: $part, $(@$input)? $($in),* => $out);
            )*
        )*
    }
}
