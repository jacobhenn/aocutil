use std::{
    array, cmp,
    collections::{hash_map::DefaultHasher, HashMap},
    env,
    fmt::{self, Display},
    hash::{Hash, Hasher},
    io,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Add, RangeInclusive},
    ptr,
    str::FromStr,
};

use itertools::Itertools;

use num::{One, Signed};

use tracing_subscriber::{fmt::format::FmtSpan, util::SubscriberInitExt, EnvFilter};

pub mod vector;

pub mod grid;

pub mod parse;

pub mod metric;

pub mod graph;

pub mod range;

pub mod range_set;

pub mod prelude {
    pub use super::{graph::*, grid::*, metric::*, parse::*, range::*, range_set::*, vector::*, *};

    pub use std::{
        collections::*,
        fmt::{Debug, Display, Write},
        *,
    };

    pub use tracing::*;

    pub use tracing_subscriber::util::SubscriberInitExt;

    pub use itertools::{self, Itertools};
}

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

pub struct Ints<'a, T> {
    src: &'a str,
    _marker: PhantomData<T>,
}

impl<'a, T> Iterator for Ints<'a, T>
where
    T: FromStr + IsSigned,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let next_num_start = self
            .src
            .find(|c: char| c.is_ascii_digit() || (T::IS_SIGNED && c == '-'))?;
        self.src = &self.src[next_num_start..];
        if let Some(next_num_end) = self.src[1..].find(|c: char| !c.is_ascii_digit()) {
            let Ok(res) = self.src[..(next_num_end + 1)].parse::<T>()
            else { return self.next() };
            self.src = &self.src[(next_num_end + 1)..];
            Some(res)
        } else {
            let Ok(res) = self.src.parse::<T>()
            else { return self.next() };
            self.src = "";
            Some(res)
        }
    }
}

pub fn ints<T>(src: &str) -> Ints<T> {
    Ints {
        src,
        _marker: PhantomData,
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
}

impl<T> IteratorExt for T where T: Iterator {}

pub fn transpose<T>(vecs: Vec<Vec<T>>) -> Vec<Vec<T>>
where
    T: Clone,
{
    let mut out = Vec::new();
    let Some(max_len) = vecs.iter().map(Vec::len).max() else { return out; };
    for i in 0..max_len {
        let mut col = Vec::new();
        for vec in &vecs {
            let Some(i) = vec.get(i) else { continue; };
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

pub trait RangeExt<T> {
    fn ordered(left: T, right: T) -> Self
    where
        T: PartialOrd;

    fn intersects(&self, other: &Self) -> bool
    where
        T: PartialOrd;

    fn contains_range(&self, val: &Self) -> bool
    where
        T: PartialOrd;

    fn touches(&self, other: &Self) -> bool
    where
        T: PartialOrd + Add<Output = T> + One + Clone;

    fn combine(self, other: Self) -> Self
    where
        T: Ord;

    fn intersection(self, other: Self) -> Self
    where
        T: Ord;

    fn pretty_print(&self) -> String
    where
        T: Display;
}

impl<T> RangeExt<T> for RangeInclusive<T> {
    fn ordered(left: T, right: T) -> Self
    where
        T: PartialOrd,
    {
        if left < right {
            left..=right
        } else {
            right..=left
        }
    }

    fn intersects(&self, other: &Self) -> bool
    where
        T: PartialOrd,
    {
        (self.start() <= other.end() && self.end() >= other.start())
            || (other.start() <= self.end() && other.end() >= self.start())
    }

    fn contains_range(&self, other: &Self) -> bool
    where
        T: PartialOrd,
    {
        self.start() <= other.start() && self.end() >= other.end()
    }

    fn touches(&self, other: &Self) -> bool
    where
        T: PartialOrd + Add<Output = T> + One + Clone,
    {
        self.intersects(other)
            || self.end().clone() + T::one() == *other.end()
            || other.end().clone() + T::one() == *other.start()
    }

    fn combine(self, other: Self) -> Self
    where
        T: Ord,
    {
        let (self_start, self_end) = self.into_inner();
        let (other_start, other_end) = other.into_inner();
        cmp::min(self_start, other_start)..=cmp::max(self_end, other_end)
    }

    fn intersection(self, other: Self) -> Self
    where
        T: Ord,
    {
        let (self_start, self_end) = self.into_inner();
        let (other_start, other_end) = other.into_inner();
        cmp::max(self_start, other_start)..=cmp::min(self_end, other_end)
    }

    fn pretty_print(&self) -> String
    where
        T: Display,
    {
        format!("{}..{}", self.start(), self.end())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PlaneAxis {
    Horizontal,
    Vertical,
}

impl PlaneAxis {
    pub fn iter() -> impl Iterator<Item = Self> {
        [Self::Horizontal, Self::Vertical].into_iter()
    }

    pub fn other(self) -> Self {
        match self {
            PlaneAxis::Horizontal => PlaneAxis::Vertical,
            PlaneAxis::Vertical => PlaneAxis::Horizontal,
        }
    }
}

impl Display for PlaneAxis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PlaneAxis::Horizontal => f.write_str("horizontal"),
            PlaneAxis::Vertical => f.write_str("vertical"),
        }
    }
}

pub fn display_range<T>(range: &RangeInclusive<T>) -> String
where
    T: Display,
{
    format!("{}..{}", range.start(), range.end())
}

pub fn default_logger() -> impl SubscriberInitExt {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .without_time()
        .with_target(false)
        .with_line_number(true)
}

pub fn test_logger() -> impl SubscriberInitExt {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .without_time()
        .with_target(false)
        .with_line_number(true)
        .with_test_writer()
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Part {
    One,
    Two,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Context {
    pub part: Part,
    pub example: Option<usize>,
}

impl Context {
    pub fn is_part_one(self) -> bool {
        self.part == Part::One
    }

    pub fn is_part_two(self) -> bool {
        self.part == Part::Two
    }

    pub fn is_example(self) -> bool {
        self.example.is_some()
    }

    pub fn is_actual(self) -> bool {
        self.example.is_none()
    }

    pub fn example(part: Part, n: usize) -> Self {
        Self {
            part,
            example: Some(n),
        }
    }

    pub fn actual(part: Part) -> Self {
        Self {
            part,
            example: None,
        }
    }
}

pub fn get_input(day: usize) -> String {
    std::fs::read_to_string(format!(
        "{}/{day}",
        env::var("AOC22_INPUT_DIR").expect("environment variable AOC22_INPUT_DIR should be set")
    ))
    .expect("input file should be present")
}

#[macro_export]
macro_rules! example_tests {
    {
        part one:
            $($p1n:ident: $p1in:expr => $p1out:literal),*
        part two:
            $($p2n:ident: $p2in:expr => $p2out:literal),*
    } => {
        $(
            #[test]
            fn $p1n() {
                let _ = aocutil::test_logger().try_init();
                assert_eq!(solve($p1in, Context::example(Part::One, 0)), $p1out);
            }
        ),*

        $(
            #[test]
            fn $p2n() {
                let _ = aocutil::test_logger().try_init();
                assert_eq!(solve($p2in, Context::example(Part::Two, 0)), $p2out);
            }
        ),*
    }
}
