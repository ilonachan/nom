use std::fmt;

use crate::{
    branch::alt, bytes::complete::{is_a, tag, take_while1}, combinator::{map_res, opt}, sequence::delimited, AsChar, IResult, Parser
};

use super::{pratt, binary_closure, unary_closure, consume_closures};

#[derive(Debug, Clone)]
enum Expr<'a> {
    Constant(isize),
    Atom(&'a str),
    Prefix(char, Box<Expr<'a>>),
    Postfix(char, Box<Expr<'a>>),
    Infix(char, Box<Expr<'a>>, Box<Expr<'a>>),
    Group(Box<Expr<'a>>),
    Ternary(Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
}
impl fmt::Display for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Constant(i) => write!(f, "{i}"),
            Expr::Atom(i) => write!(f, "{i}"),
            Expr::Prefix(i, s) | Expr::Postfix(i, s) => write!(f, "({i} {s})"),
            Expr::Infix(i, s1, s2) => write!(f, "({i} {s1} {s2})"),
            Expr::Group(s) => write!(f, "(group {s})"),
            Expr::Ternary(l, m, r) => write!(f, "(? {l} {m} {r})"),
        }
    }
}

type E<'a> = crate::error::Error<&'a str>;

fn expr(i: &str, fold_constants: bool) -> IResult<&str, Expr> {
    fn expr_pratt_parser(i: &str, fold_constants: bool, start_bp: usize) -> IResult<&str, Expr> {
        fn first_char(s: &str) -> char {
            s.chars().next().unwrap()
        }
        fn map_infix<'a, F>(
            fold: bool,
            mut fold_const: F,
        ) -> impl FnMut(&'a str, &'a str, Expr<'a>, Expr<'a>) -> IResult<&'a str, Expr<'a>>
        where
            F: FnMut(&'a str, isize, isize) -> Option<isize>,
        {
            move |i, op, lhs, rhs| {
                Ok((
                    i,
                    match (lhs, rhs, fold) {
                        (Expr::Constant(a), Expr::Constant(b), true) => {
                            if let Some(c) = fold_const(op, a, b) {
                                Expr::Constant(c)
                            } else {
                                Expr::Infix(
                                    first_char(op),
                                    Box::new(Expr::Constant(a)),
                                    Box::new(Expr::Constant(b)),
                                )
                            }
                        }
                        (lhs, rhs, _) => Expr::Infix(first_char(op), Box::new(lhs), Box::new(rhs)),
                    },
                ))
            }
        }
        fn map_prefix<'a, F>(
            fold: bool,
            mut fold_const: F,
        ) -> impl FnMut(&'a str, &'a str, Expr<'a>) -> IResult<&'a str, Expr<'a>>
        where
            F: FnMut(&'a str, isize) -> Option<isize>,
        {
            move |i, op, wrapped| {
                Ok((
                    i,
                    match (wrapped, fold) {
                        (Expr::Constant(a), true) => {
                            if let Some(c) = fold_const(op, a) {
                                Expr::Constant(c)
                            } else {
                                Expr::Prefix(first_char(op), Box::new(Expr::Constant(a)))
                            }
                        }
                        (wrapped, _) => Expr::Prefix(first_char(op), Box::new(wrapped)),
                    },
                ))
            }
        }
        fn map_postfix<'a, F>(
            fold: bool,
            mut fold_const: F,
        ) -> impl FnMut(&'a str, &'a str, Expr<'a>) -> IResult<&'a str, Expr<'a>>
        where
            F: FnMut(&'a str, isize) -> Option<isize>,
        {
            move |i, op, wrapped| {
                Ok((
                    i,
                    match (wrapped, fold) {
                        (Expr::Constant(a), true) => {
                            if let Some(c) = fold_const(op, a) {
                                Expr::Constant(c)
                            } else {
                                Expr::Postfix(first_char(op), Box::new(Expr::Constant(a)))
                            }
                        }
                        (wrapped, _) => Expr::Postfix(first_char(op), Box::new(wrapped)),
                    },
                ))
            }
        }

        fn atom(i: &str) -> IResult<&str, Expr> {
            delimited(
                opt(is_a(" ")),
                map_res(
                    take_while1(|i: char| i.is_alphanum()),
                    |c: &str| {
                        Ok::<_, ()>(match c.parse() {
                            Ok(val) => Expr::Constant(val),
                            Err(_) => Expr::Atom(c),
                        })
                    },
                ),
                opt(is_a(" ")),
            )
            .parse(i)
        }

        let group_op = unary_closure(tag("("), 0, |i, _, rhs| {
            let (i, _) = tag(")").parse(i)?;
            Ok((i, Expr::Group(Box::new(rhs))))
        });

        let index_op = unary_closure(tag("["), 11, |i, _, lhs| {
            let (i, rhs) = expr_pratt_parser(i, fold_constants, 0)?;
            let (i, _) = tag("]").parse(i)?;
            Ok((i, Expr::Infix('[', Box::new(lhs), Box::new(rhs))))
        });

        let ternary_op = binary_closure(tag("?"), 4, 0, |i, _, lhs, mhs| {
            let (i, _) = tag(":").parse(i)?;
            let (i, rhs) = expr_pratt_parser(i, fold_constants, 3)?;
            Ok((
                i,
                Expr::Ternary(Box::new(lhs), Box::new(mhs), Box::new(rhs)),
            ))
        });

        pratt(
            atom,
            alt((
                binary_closure(tag("="), 2, 1, map_infix(fold_constants, |_, _, _| None)),
                ternary_op,
                binary_closure(
                    tag("+").or(tag("-")),
                    5,
                    6,
                    map_infix(fold_constants, |op, a, b| {
                        Some(if op == "+" { a + b } else { a - b })
                    }),
                ),
                binary_closure(
                    tag("*"),
                    7,
                    8,
                    map_infix(fold_constants, |_, a, b| Some(a * b)),
                ),
                binary_closure(
                    tag("/"),
                    7,
                    8,
                    map_infix(fold_constants, |_, a, b| Some(a / b)),
                ),
                binary_closure(tag("."), 14, 13, map_infix(fold_constants, |_, _, _| None)),
            )),
            alt((
                unary_closure(
                    tag::<&str, &str, E>("+").or(tag("-")),
                    9,
                    map_prefix(fold_constants, |op, a| Some(if op == "-" { -a } else { a })),
                ),
                group_op,
            )),
            alt((
                unary_closure(tag("!"), 11, map_postfix(fold_constants, |_, _| None)),
                index_op,
            )),
            consume_closures(|_, _| unreachable!()),
            start_bp,
        )
        .parse(i)
    }
    expr_pratt_parser(i, fold_constants, 0)
}

fn test_ok(input: &str, output: &str, remainder: &str) {
    let (rem, s) = expr(input, false).unwrap();
    assert_eq!((rem, s.to_string().as_str()), (remainder, output));
}

#[test]
fn test_pratt() {
    test_ok("  1 ", "1", "");
    test_ok("1 + 2 * 3", "(+ 1 (* 2 3))", "");
    test_ok("a + b * c * d + e", "(+ (+ a (* (* b c) d)) e)", "");
    test_ok("f . g . h", "(. f (. g h))", "");
    test_ok(
        " 1 + 2 + f . g . h * 3 * 4",
        "(+ (+ 1 2) (* (* (. f (. g h)) 3) 4))",
        "",
    );

    test_ok("--1 * 2", "(* (- (- 1)) 2)", "");
    test_ok("--f . g", "(- (- (. f g)))", "");

    test_ok("-9!", "(- (! 9))", "");
    test_ok("f . g !", "(! (. f g))", "");

    test_ok("(((0)))", "(group (group (group 0)))", "");

    test_ok("x[0][1]", "([ ([ x 0) 1)", "");
    test_ok("a ? b : c ? d : e", "(? a b (? c d e))", "");
    test_ok("a = 0 ? b : c = d", "(= a (= (? 0 b c) d))", "");
}
