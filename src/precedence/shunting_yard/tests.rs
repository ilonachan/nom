use super::{binary_op, shunting_yard, unary_op, Assoc, OperatorCall};
use crate::{
    branch::alt,
    bytes::complete::tag,
    character::complete::digit1,
    combinator::{fail, map_res},
    error::ErrorKind,
    error_node_position, error_position,
    sequence::delimited,
    IResult, Parser,
};

fn parser(i: &str) -> IResult<&str, i64> {
    shunting_yard(
        alt((
            map_res(digit1, |s: &str| s.parse::<i64>()),
            delimited(tag("("), parser, tag(")")),
        )),
        alt((
            binary_op(tag("*"), 2, Assoc::Left),
            binary_op(tag("/"), 2, Assoc::Left),
            binary_op(tag("+"), 3, Assoc::Left),
            binary_op(tag("-"), 3, Assoc::Left),
        )),
        unary_op(tag("-"), 1),
        fail(),
        |op: OperatorCall<&str, &str, (), i64>| {
            use super::OperatorCall::*;
            match op {
                Prefix("-", o) => Ok(-o),
                Infix(lhs, "*", rhs) => Ok(lhs * rhs),
                Infix(lhs, "/", rhs) => Ok(lhs / rhs),
                Infix(lhs, "+", rhs) => Ok(lhs + rhs),
                Infix(lhs, "-", rhs) => Ok(lhs - rhs),
                _ => Err("Invalid combination"),
            }
        },
    )
    .parse(i)
}

#[test]
fn precedence_test() {
    assert_eq!(parser("3"), Ok(("", 3)));
    assert_eq!(parser("-3"), Ok(("", -3)));
    assert_eq!(parser("4-(2*2)"), Ok(("", 0)));
    assert_eq!(parser("4-2*2"), Ok(("", 0)));
    assert_eq!(parser("(4-2)*2"), Ok(("", 4)));
    assert_eq!(parser("2*2/1"), Ok(("", 4)));

    let a = "a";

    assert_eq!(
        parser(a),
        Err(crate::Err::Error(error_node_position!(
            a,
            ErrorKind::Tag,
            error_position!(a, ErrorKind::Tag)
        )))
    );

    let b = "3+b";

    assert_eq!(
        parser(b),
        Err(crate::Err::Error(error_node_position!(
            &b[2..],
            ErrorKind::Tag,
            error_position!(&b[2..], ErrorKind::Tag)
        )))
    );
}
