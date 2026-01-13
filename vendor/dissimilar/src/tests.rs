#![allow(
    clippy::incompatible_msrv, // https://github.com/rust-lang/rust-clippy/issues/12257
)]

use super::*;
use std::sync::OnceLock;

macro_rules! range {
    ($text:expr) => {{
        static CHARS: OnceLock<Vec<char>> = OnceLock::new();
        let chars = CHARS.get_or_init(|| $text.chars().collect());
        Range::new(chars, ..)
    }};
}

macro_rules! diff_list {
    () => {
        Solution {
            text1: Range::empty(),
            text2: Range::empty(),
            diffs: Vec::new(),
        }
    };
    ($($kind:ident($text:literal)),+ $(,)?) => {{
        #[allow(unused_macro_rules)]
        macro_rules! text1 {
            (Insert, $s:literal) => { "" };
            (Delete, $s:literal) => { $s };
            (Equal, $s:literal) => { $s };
        }
        #[allow(unused_macro_rules)]
        macro_rules! text2 {
            (Insert, $s:literal) => { $s };
            (Delete, $s:literal) => { "" };
            (Equal, $s:literal) => { $s };
        }
        let text1 = range!(concat!($(text1!($kind, $text)),*));
        let text2 = range!(concat!($(text2!($kind, $text)),*));
        let (_i, _j) = (&mut 0, &mut 0);
        #[allow(unused_macro_rules)]
        macro_rules! range {
            (Insert, $s:literal) => {
                Diff::Insert(range(text2.doc, _j, $s))
            };
            (Delete, $s:literal) => {
                Diff::Delete(range(text1.doc, _i, $s))
            };
            (Equal, $s:literal) => {
                Diff::Equal(range(text1.doc, _i, $s), range(text2.doc, _j, $s))
            };
        }
        Solution {
            text1,
            text2,
            diffs: vec![$(range!($kind, $text)),*],
        }
    }};
}

fn range<'a>(doc: &'a [char], offset: &mut usize, text: &str) -> Range<'a> {
    let len = text.chars().count();
    let range = Range {
        doc,
        offset: *offset,
        len,
    };
    *offset += len;
    range
}

macro_rules! assert_diffs {
    ([$($kind:ident($text:literal)),* $(,)?], $solution:ident, $msg:expr $(,)?) => {
        let expected = &[$(Chunk::$kind($text)),*];
        assert!(
            same_diffs(expected, &$solution.diffs),
            concat!($msg, "\nexpected={:#?}\nactual={:#?}"),
            expected, $solution.diffs,
        );
    };
}

fn same_diffs(expected: &[Chunk], actual: &[Diff]) -> bool {
    fn eq(expected: &str, actual: &Range) -> bool {
        expected.chars().eq(slice(*actual).iter().copied())
    }

    expected.len() == actual.len()
        && expected.iter().zip(actual).all(|pair| match pair {
            (Chunk::Insert(expected), Diff::Insert(actual)) => eq(expected, actual),
            (Chunk::Delete(expected), Diff::Delete(actual)) => eq(expected, actual),
            (Chunk::Equal(expected), Diff::Equal(actual1, actual2)) => {
                eq(expected, actual1) && eq(expected, actual2)
            }
            (_, _) => false,
        })
}

#[test]
fn test_common_prefix() {
    let text1 = range!("abc");
    let text2 = range!("xyz");
    assert_eq!(0, common_prefix(text1, text2), "Null case");

    let text1 = range!("1234abcdef");
    let text2 = range!("1234xyz");
    assert_eq!(4, common_prefix(text1, text2), "Non-null case");

    let text1 = range!("1234");
    let text2 = range!("1234xyz");
    assert_eq!(4, common_prefix(text1, text2), "Whole case");
}

#[test]
fn test_common_suffix() {
    let text1 = range!("abc");
    let text2 = range!("xyz");
    assert_eq!(0, common_suffix(text1, text2), "Null case");

    let text1 = range!("abcdef1234");
    let text2 = range!("xyz1234");
    assert_eq!(4, common_suffix(text1, text2), "Non-null case");

    let text1 = range!("1234");
    let text2 = range!("xyz1234");
    assert_eq!(4, common_suffix(text1, text2), "Whole case");
}

#[test]
fn test_common_overlap() {
    let text1 = Range::empty();
    let text2 = range!("abcd");
    assert_eq!(0, common_overlap(text1, text2), "Null case");

    let text1 = range!("abc");
    let text2 = range!("abcd");
    assert_eq!(3, common_overlap(text1, text2), "Whole case");

    let text1 = range!("123456");
    let text2 = range!("abcd");
    assert_eq!(0, common_overlap(text1, text2), "No overlap");

    let text1 = range!("123456xxx");
    let text2 = range!("xxxabcd");
    assert_eq!(3, common_overlap(text1, text2), "Overlap");

    // Some overly clever languages (C#) may treat ligatures as equal to their
    // component letters. E.g. U+FB01 == 'fi'
    let text1 = range!("fi");
    let text2 = range!("\u{fb01}i");
    assert_eq!(0, common_overlap(text1, text2), "Unicode");
}

#[test]
fn test_cleanup_merge() {
    let mut solution = diff_list![];
    cleanup_merge(&mut solution);
    assert_diffs!([], solution, "Null case");

    let mut solution = diff_list![Equal("a"), Delete("b"), Insert("c")];
    cleanup_merge(&mut solution);
    assert_diffs!(
        [Equal("a"), Delete("b"), Insert("c")],
        solution,
        "No change case",
    );

    let mut solution = diff_list![Equal("a"), Equal("b"), Equal("c")];
    cleanup_merge(&mut solution);
    assert_diffs!([Equal("abc")], solution, "Merge equalities");

    let mut solution = diff_list![Delete("a"), Delete("b"), Delete("c")];
    cleanup_merge(&mut solution);
    assert_diffs!([Delete("abc")], solution, "Merge deletions");

    let mut solution = diff_list![Insert("a"), Insert("b"), Insert("c")];
    cleanup_merge(&mut solution);
    assert_diffs!([Insert("abc")], solution, "Merge insertions");

    let mut solution = diff_list![
        Delete("a"),
        Insert("b"),
        Delete("c"),
        Insert("d"),
        Equal("e"),
        Equal("f"),
    ];
    cleanup_merge(&mut solution);
    assert_diffs!(
        [Delete("ac"), Insert("bd"), Equal("ef")],
        solution,
        "Merge interweave",
    );

    let mut solution = diff_list![Delete("a"), Insert("abc"), Delete("dc")];
    cleanup_merge(&mut solution);
    assert_diffs!(
        [Equal("a"), Delete("d"), Insert("b"), Equal("c")],
        solution,
        "Prefix and suffix detection",
    );

    let mut solution = diff_list![
        Equal("x"),
        Delete("a"),
        Insert("abc"),
        Delete("dc"),
        Equal("y"),
    ];
    cleanup_merge(&mut solution);
    assert_diffs!(
        [Equal("xa"), Delete("d"), Insert("b"), Equal("cy")],
        solution,
        "Prefix and suffix detection with equalities",
    );

    let mut solution = diff_list![Equal("a"), Insert("ba"), Equal("c")];
    cleanup_merge(&mut solution);
    assert_diffs!([Insert("ab"), Equal("ac")], solution, "Slide edit left");

    let mut solution = diff_list![Equal("c"), Insert("ab"), Equal("a")];
    cleanup_merge(&mut solution);
    assert_diffs!([Equal("ca"), Insert("ba")], solution, "Slide edit right");

    let mut solution = diff_list![
        Equal("a"),
        Delete("b"),
        Equal("c"),
        Delete("ac"),
        Equal("x"),
    ];
    cleanup_merge(&mut solution);
    assert_diffs!(
        [Delete("abc"), Equal("acx")],
        solution,
        "Slide edit left recursive",
    );

    let mut solution = diff_list![
        Equal("x"),
        Delete("ca"),
        Equal("c"),
        Delete("b"),
        Equal("a"),
    ];
    cleanup_merge(&mut solution);
    assert_diffs!(
        [Equal("xca"), Delete("cba")],
        solution,
        "Slide edit right recursive",
    );

    let mut solution = diff_list![Delete("b"), Insert("ab"), Equal("c")];
    cleanup_merge(&mut solution);
    assert_diffs!([Insert("a"), Equal("bc")], solution, "Empty range");

    let mut solution = diff_list![Equal(""), Insert("a"), Equal("b")];
    cleanup_merge(&mut solution);
    assert_diffs!([Insert("a"), Equal("b")], solution, "Empty equality");
}

#[test]
fn test_cleanup_semantic_lossless() {
    let mut solution = diff_list![];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!([], solution, "Null case");

    let mut solution = diff_list![
        Equal("AAA\r\n\r\nBBB"),
        Insert("\r\nDDD\r\n\r\nBBB"),
        Equal("\r\nEEE"),
    ];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!(
        [
            Equal("AAA\r\n\r\n"),
            Insert("BBB\r\nDDD\r\n\r\n"),
            Equal("BBB\r\nEEE"),
        ],
        solution,
        "Blank lines",
    );

    let mut solution = diff_list![Equal("AAA\r\nBBB"), Insert(" DDD\r\nBBB"), Equal(" EEE")];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!(
        [Equal("AAA\r\n"), Insert("BBB DDD\r\n"), Equal("BBB EEE")],
        solution,
        "Line boundaries",
    );

    let mut solution = diff_list![Equal("The c"), Insert("ow and the c"), Equal("at.")];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!(
        [Equal("The "), Insert("cow and the "), Equal("cat.")],
        solution,
        "Word boundaries",
    );

    let mut solution = diff_list![Equal("The-c"), Insert("ow-and-the-c"), Equal("at.")];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!(
        [Equal("The-"), Insert("cow-and-the-"), Equal("cat.")],
        solution,
        "Alphanumeric boundaries",
    );

    let mut solution = diff_list![Equal("a"), Delete("a"), Equal("ax")];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!([Delete("a"), Equal("aax")], solution, "Hitting the start");

    let mut solution = diff_list![Equal("xa"), Delete("a"), Equal("a")];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!([Equal("xaa"), Delete("a")], solution, "Hitting the end");

    let mut solution = diff_list![Equal("The xxx. The "), Insert("zzz. The "), Equal("yyy.")];
    cleanup_semantic_lossless(&mut solution);
    assert_diffs!(
        [Equal("The xxx."), Insert(" The zzz."), Equal(" The yyy.")],
        solution,
        "Sentence boundaries",
    );
}

#[test]
fn test_cleanup_semantic() {
    let mut solution = diff_list![];
    cleanup_semantic(&mut solution);
    assert_diffs!([], solution, "Null case");

    let mut solution = diff_list![Delete("ab"), Insert("cd"), Equal("12"), Delete("e")];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Delete("ab"), Insert("cd"), Equal("12"), Delete("e")],
        solution,
        "No elimination #1",
    );

    let mut solution = diff_list![Delete("abc"), Insert("ABC"), Equal("1234"), Delete("wxyz")];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Delete("abc"), Insert("ABC"), Equal("1234"), Delete("wxyz")],
        solution,
        "No elimination #2",
    );

    let mut solution = diff_list![Delete("a"), Equal("b"), Delete("c")];
    cleanup_semantic(&mut solution);
    assert_diffs!([Delete("abc"), Insert("b")], solution, "Simple elimination",);

    let mut solution = diff_list![
        Delete("ab"),
        Equal("cd"),
        Delete("e"),
        Equal("f"),
        Insert("g"),
    ];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Delete("abcdef"), Insert("cdfg")],
        solution,
        "Backpass elimination",
    );

    let mut solution = diff_list![
        Insert("1"),
        Equal("A"),
        Delete("B"),
        Insert("2"),
        Equal("_"),
        Insert("1"),
        Equal("A"),
        Delete("B"),
        Insert("2"),
    ];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Delete("AB_AB"), Insert("1A2_1A2")],
        solution,
        "Multiple elimination",
    );

    let mut solution = diff_list![Equal("The c"), Delete("ow and the c"), Equal("at.")];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Equal("The "), Delete("cow and the "), Equal("cat.")],
        solution,
        "Word boundaries",
    );

    let mut solution = diff_list![Delete("abcxx"), Insert("xxdef")];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Delete("abcxx"), Insert("xxdef")],
        solution,
        "No overlap elimination",
    );

    let mut solution = diff_list![Delete("abcxxx"), Insert("xxxdef")];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Delete("abc"), Equal("xxx"), Insert("def")],
        solution,
        "Overlap elimination",
    );

    let mut solution = diff_list![Delete("xxxabc"), Insert("defxxx")];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [Insert("def"), Equal("xxx"), Delete("abc")],
        solution,
        "Reverse overlap elimination",
    );

    let mut solution = diff_list![
        Delete("abcd1212"),
        Insert("1212efghi"),
        Equal("----"),
        Delete("A3"),
        Insert("3BC"),
    ];
    cleanup_semantic(&mut solution);
    assert_diffs!(
        [
            Delete("abcd"),
            Equal("1212"),
            Insert("efghi"),
            Equal("----"),
            Delete("A"),
            Equal("3"),
            Insert("BC"),
        ],
        solution,
        "Two overlap eliminations",
    );
}

#[test]
fn test_bisect() {
    let text1 = range!("cat");
    let text2 = range!("map");
    let solution = Solution {
        text1,
        text2,
        diffs: bisect(text1, text2),
    };
    assert_diffs!(
        [
            Delete("c"),
            Insert("m"),
            Equal("a"),
            Delete("t"),
            Insert("p"),
        ],
        solution,
        "Normal",
    );
}

#[test]
fn test_main() {
    let solution = main(Range::empty(), Range::empty());
    assert_diffs!([], solution, "Null case");

    let solution = main(range!("abc"), range!("abc"));
    assert_diffs!([Equal("abc")], solution, "Equality");

    let solution = main(range!("abc"), range!("ab123c"));
    assert_diffs!(
        [Equal("ab"), Insert("123"), Equal("c")],
        solution,
        "Simple insertion",
    );

    let solution = main(range!("a123bc"), range!("abc"));
    assert_diffs!(
        [Equal("a"), Delete("123"), Equal("bc")],
        solution,
        "Simple deletion",
    );

    let solution = main(range!("abc"), range!("a123b456c"));
    assert_diffs!(
        [
            Equal("a"),
            Insert("123"),
            Equal("b"),
            Insert("456"),
            Equal("c"),
        ],
        solution,
        "Two insertions",
    );

    let solution = main(range!("a123b456c"), range!("abc"));
    assert_diffs!(
        [
            Equal("a"),
            Delete("123"),
            Equal("b"),
            Delete("456"),
            Equal("c"),
        ],
        solution,
        "Two deletions",
    );

    let solution = main(range!("a"), range!("b"));
    assert_diffs!([Delete("a"), Insert("b")], solution, "Simple case #1");

    let solution = main(
        range!("Apples are a fruit."),
        range!("Bananas are also fruit."),
    );
    assert_diffs!(
        [
            Delete("Apple"),
            Insert("Banana"),
            Equal("s are a"),
            Insert("lso"),
            Equal(" fruit."),
        ],
        solution,
        "Simple case #2",
    );

    let solution = main(range!("ax\t"), range!("\u{0680}x\000"));
    assert_diffs!(
        [
            Delete("a"),
            Insert("\u{0680}"),
            Equal("x"),
            Delete("\t"),
            Insert("\000"),
        ],
        solution,
        "Simple case #3",
    );

    let solution = main(range!("1ayb2"), range!("abxab"));
    assert_diffs!(
        [
            Delete("1"),
            Equal("a"),
            Delete("y"),
            Equal("b"),
            Delete("2"),
            Insert("xab"),
        ],
        solution,
        "Overlap #1",
    );

    let solution = main(range!("abcy"), range!("xaxcxabc"));
    assert_diffs!(
        [Insert("xaxcx"), Equal("abc"), Delete("y")],
        solution,
        "Overlap #2",
    );

    let solution = main(
        range!("ABCDa=bcd=efghijklmnopqrsEFGHIJKLMNOefg"),
        range!("a-bcd-efghijklmnopqrs"),
    );
    assert_diffs!(
        [
            Delete("ABCD"),
            Equal("a"),
            Delete("="),
            Insert("-"),
            Equal("bcd"),
            Delete("="),
            Insert("-"),
            Equal("efghijklmnopqrs"),
            Delete("EFGHIJKLMNOefg"),
        ],
        solution,
        "Overlap #3",
    );

    let solution = main(
        range!("a [[Pennsylvania]] and [[New"),
        range!(" and [[Pennsylvania]]"),
    );
    assert_diffs!(
        [
            Insert(" "),
            Equal("a"),
            Insert("nd"),
            Equal(" [[Pennsylvania]]"),
            Delete(" and [[New"),
        ],
        solution,
        "Large equality",
    );
}
