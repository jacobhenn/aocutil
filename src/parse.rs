#[macro_export]
macro_rules! unlist {
    ($src:expr, $($name:ident),+) => {
        let mut iter = $src.into_iter();
        $(
            let $name = iter.next().unwrap();
        )+
    }
}

#[test]
fn test_unlist() {
    unlist!(super::ints::<i32>("-57     89     -24&&78"), a, b, c, d);
    assert_eq!(a, -57);
    assert_eq!(b, 89);
    assert_eq!(c, -24);
    assert_eq!(d, 78);
}

#[test]
#[should_panic]
fn test_unlist_panic() {
    unlist!(super::ints::<i32>("78, 45. 89"), _a, _b, _c, _d, _e, _f, _g);
}
