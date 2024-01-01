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

#[macro_export]
macro_rules! parse {
    (
        $s:expr =>
            $($pref:literal)?
            $(($name:ident $(: $ty:ty)?) $anchor:literal)+
            $(@last ($last_name:ident $(: $last_ty:ty)?))?
    ) => {
        let mut s: &str = $s;

        $(
            if let Some(after) = s.strip_prefix($pref) {
                s = after;
            } else {
                core::panic!("aocutil::parse: expected prefix '{}', found '{}'", $pref, s);
            }
        )?

        $(
            let Some((before, after)) = s.split_once($anchor) else {
                core::panic!(
                    "aocutil::parse: expected '{}', found '{}' when looking for `{}`",
                    $anchor,
                    s,
                    stringify!($name),
                );
            };

            #[allow(unused_variables)]
            let $name: &str = before;

            $(
                let $name = match <$ty as core::str::FromStr>::from_str(before) {
                    Ok(ok) => ok,
                    Err(err) => {
                        core::panic!(
                            "aocutil::parse: failed to parse '{}' as `{}`: {err}",
                            before,
                            stringify!($ty),
                        )
                    },
                };
            )?

            s = after;
        )+


        $(
            #[allow(unused_variables)]
            let $last_name = s;

            $(
                let $last_name = match <$last_ty as core::str::FromStr>::from_str(s) {
                    Ok(ok) => ok,
                    Err(err) => {
                        core::panic!(
                            "aocutil::parse: failed to parse '{}' as `{}`: {err}",
                            before,
                            stringify!($last_ty),
                        )
                    },
                };
            )?
        )?
    }
}

#[test]
fn test_parse_2023_4() {
    let s = "Card 1: 41 48 | 83 86";

    parse!(s => "Card " (_n) ": " (have) " | " @last (winning));

    assert_eq!(have, "41 48");
    assert_eq!(winning, "83 86");
}

#[test]
fn test_parse_2023_7() {
    let s = "32T3K 765";

    parse!(s => (hand) " " @last (bid: u32));

    assert_eq!(hand, "32T3K");
    assert_eq!(bid, 765);
}

#[test]
#[allow(unused_assignments)]
fn test_parse_2023_8() {
    let s = "AAA = (BBB, CCC)";

    parse!(s => (node) " = (" (left) ", " (right) ")");

    assert_eq!(node, "AAA");
    assert_eq!(left, "BBB");
    assert_eq!(right, "CCC");
}

#[test]
#[allow(unused_assignments)]
fn test_parse_2023_18() {
    let s = "R 6 (#70c710)";

    parse!(s => (direction) " " (step: i32) " (#" (color) ")");

    assert_eq!(direction, "R");
    assert_eq!(step, 6);
    assert_eq!(color, "70c710");
}
